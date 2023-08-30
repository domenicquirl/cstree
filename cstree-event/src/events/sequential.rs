use super::{Event, __private::EventSinkInternal};

#[derive(Debug, Default)]
#[repr(transparent)]
pub struct SequentialEventSink<S: cstree::Syntax> {
    inner: Vec<Event<S>>,
}

impl<S: cstree::Syntax> SequentialEventSink<S> {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
        }
    }
}

impl<S: cstree::Syntax> EventSinkInternal<S> for SequentialEventSink<S> {
    #[inline]
    fn add(&mut self, event: Event<S>) {
        self.inner.push(event);
    }

    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }

    fn assert_complete(&self) {
        match &self.inner[0] {
            Event::Enter { .. } => match &self.inner[self.inner.len() - 1] {
                Event::Exit => {}
                _ => panic!("Event sequence starting with `Enter` does not end with `Exit`"),
            },
            _ => panic!("Event sequence does not start with `Enter` or `DeOpt`"),
        }
    }

    #[inline]
    fn into_inner(self) -> Vec<Event<S>> {
        self.inner
    }

    #[inline]
    fn inner(&self) -> &Vec<Event<S>> {
        &self.inner
    }

    #[inline]
    fn inner_mut(&mut self) -> &mut Vec<Event<S>> {
        &mut self.inner
    }

    #[inline(always)]
    fn currently_deopt(&self) -> bool {
        // NOTE(DQ): the sequential event sink always buffers all events
        true
    }
}

impl<S: cstree::Syntax> AsRef<[Event<S>]> for SequentialEventSink<S> {
    fn as_ref(&self) -> &[Event<S>] {
        self.inner.as_ref()
    }
}

impl<S: cstree::Syntax> AsMut<[Event<S>]> for SequentialEventSink<S> {
    fn as_mut(&mut self) -> &mut [Event<S>] {
        self.inner.as_mut()
    }
}

#[cfg(test)]
mod tests {
    use core::num::NonZeroUsize;

    use cstree::testing::TestSyntaxKind;

    use crate::events::EventSink;

    use super::*;

    #[test]
    fn basic() {
        let mut events = SequentialEventSink::with_capacity(10);
        assert!(events.is_empty());
        assert!(events.currently_deopt());
        let root = events.enter_node(TestSyntaxKind::Root);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
            n_input_tokens: 1,
        });
        root.complete(&mut events);
        assert_eq!(events.len(), 3);
        events.assert_complete();
    }

    #[test]
    fn discard() {
        let mut events = SequentialEventSink::with_capacity(10);
        let root = events.enter_node(TestSyntaxKind::Root);
        let inner = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
            n_input_tokens: 1,
        });
        inner.discard(&mut events);
        root.complete(&mut events);
        assert_eq!(events.len(), 2);
        assert_eq!(
            events.inner()[0],
            Event::Enter {
                kind:        TestSyntaxKind::Root,
                preceded_by: None,
            }
        );
        events.assert_complete();
    }

    #[test]
    fn abandon() {
        let mut events = SequentialEventSink::with_capacity(10);
        let root = events.enter_node(TestSyntaxKind::Root);
        let inner = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
            n_input_tokens: 1,
        });
        inner.abandon(&mut events);
        root.complete(&mut events);
        assert_eq!(events.len(), 4);
        assert_eq!(events.inner()[1], Event::Placeholder);
        events.assert_complete();
    }

    #[test]
    fn complete_as() {
        let mut events = SequentialEventSink::with_capacity(10);
        let root = events.enter_node(TestSyntaxKind::Root);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
            n_input_tokens: 1,
        });
        root.complete_as(&mut events, Some(TestSyntaxKind::Operation));
        assert_eq!(events.len(), 3);
        assert_eq!(
            events.inner()[0],
            Event::Enter {
                kind:        TestSyntaxKind::Operation,
                preceded_by: None,
            }
        );
        events.assert_complete();
    }

    #[test]
    fn precede() {
        let mut events = SequentialEventSink::with_capacity(10);
        let op = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
            n_input_tokens: 1,
        });
        let node = op.complete(&mut events);
        let root = node.precede(&mut events, TestSyntaxKind::Root);
        root.complete(&mut events);
        assert_eq!(events.len(), 5);
        assert_eq!(
            events.inner()[0],
            Event::Enter {
                kind:        TestSyntaxKind::Operation,
                preceded_by: Some(NonZeroUsize::new(3).unwrap()),
            }
        );
        assert_eq!(
            events.inner()[3],
            Event::Enter {
                kind:        TestSyntaxKind::Root,
                preceded_by: None,
            }
        );
        events.assert_complete();
    }
}

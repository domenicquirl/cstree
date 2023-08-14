use super::{EnteredNode, Event, __private::EventSinkInternal};
use crate::channel::{self, Receiver, Sender};

#[derive(Debug)]
pub struct ConcurrentEventSink<S: cstree::Syntax + 'static> {
    inner:  Vec<Event<S>>,
    sender: Sender<Event<S>>,
    deopt:  bool,
}

impl<S: cstree::Syntax> ConcurrentEventSink<S> {
    pub fn new() -> (Self, Receiver<Event<S>>) {
        let (sender, receiver) = channel::unbounded_spsc();
        let this = Self {
            inner: Vec::new(),
            sender,
            deopt: false,
        };
        (this, receiver)
    }

    pub fn with_capacity(capacity: usize) -> (Self, Receiver<Event<S>>) {
        let (sender, receiver) = channel::unbounded_spsc();
        let this = Self {
            inner: Vec::with_capacity(capacity),
            sender,
            deopt: false,
        };
        (this, receiver)
    }
}

impl<S: cstree::Syntax> EventSinkInternal<S> for ConcurrentEventSink<S> {
    fn add(&mut self, event: Event<S>) {
        match event {
            e @ Event::DeOpt => {
                assert!(!self.deopt, "Tried to nest deopt events");
                self.deopt = true;
                self.inner.push(e);
            }
            e @ Event::Opt => {
                assert!(self.deopt, "Unmatched opt event");
                self.deopt = false;
                // After the deopt subtree is finished, send off the contained events
                self.sender
                    .send_all(self.inner.drain(..))
                    .expect("No receiver for event");
                self.sender.send(e).expect("No receiver for event");
            }
            e if self.deopt => self.inner.push(e),
            e @ Event::Enter { .. } | e @ Event::Token { .. } | e @ Event::Exit => {
                self.sender.send(e).expect("No receiver for event")
            }
            Event::Placeholder => panic!("Tried to add placeholder event"),
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    fn assert_complete(&self) {
        assert!(!self.deopt);
        assert!(self.inner.is_empty());
    }

    fn into_inner(self) -> Vec<Event<S>> {
        self.inner
    }

    fn inner(&self) -> &Vec<Event<S>> {
        &self.inner
    }

    fn inner_mut(&mut self) -> &mut Vec<Event<S>> {
        &mut self.inner
    }

    fn currently_deopt(&self) -> bool {
        self.deopt
    }
}

impl<S: cstree::Syntax> ConcurrentEventSink<S> {
    pub fn deopt(&mut self) -> EnteredNode {
        let idx = self.len();
        self.add(Event::DeOpt);
        EnteredNode::new(idx, true)
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
        let (mut events, receiver) = ConcurrentEventSink::with_capacity(10);
        assert!(events.is_empty());
        assert!(!events.currently_deopt());
        let root = events.enter_node(TestSyntaxKind::Root);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        root.complete(&mut events);
        assert_eq!(events.len(), 0);
        events.assert_complete();

        let events: Vec<_> = receiver.drain().collect();
        assert_eq!(events.len(), 3);
    }

    #[test]
    fn discard() {
        let (mut events, _receiver) = ConcurrentEventSink::with_capacity(10);
        let root = events.enter_node(TestSyntaxKind::Root);
        let opt_guard = events.deopt();
        let inner = events.enter_node(TestSyntaxKind::Operation);
        assert!(events.currently_deopt());
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        inner.discard(&mut events);
        // We expect the following:
        // - the enter event for `Root` should have been sent directly, as the sink was in opt
        // - then the sink buffered the events for the deopt, `inner` and the `Float` token
        // - and then everything starting from (and including) `inner` is discarded
        assert_eq!(events.len(), 1);
        opt_guard.complete(&mut events);
        assert!(!events.currently_deopt());
        root.complete(&mut events);
        events.assert_complete();
    }

    #[test]
    fn abandon() {
        let (mut events, receiver) = ConcurrentEventSink::with_capacity(10);
        let root = events.enter_node(TestSyntaxKind::Root);
        let opt_guard = events.deopt();
        let inner = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        inner.abandon(&mut events);
        opt_guard.complete(&mut events);
        root.complete(&mut events);
        events.assert_complete();

        let events: Vec<_> = receiver.drain().collect();
        assert_eq!(events.len(), 6);
        assert_eq!(events[2], Event::Placeholder);
    }

    #[test]
    fn complete_as() {
        let (mut events, receiver) = ConcurrentEventSink::with_capacity(10);
        let opt_guard = events.deopt();
        let root = events.enter_node(TestSyntaxKind::Root);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        root.complete_as(&mut events, Some(TestSyntaxKind::Operation));
        opt_guard.complete(&mut events);
        events.assert_complete();

        let events: Vec<_> = receiver.drain().collect();
        assert_eq!(events.len(), 5);
        assert_eq!(
            events[1],
            Event::Enter {
                kind:        TestSyntaxKind::Operation,
                preceded_by: None,
            }
        );
    }

    #[test]
    fn precede() {
        let (mut events, receiver) = ConcurrentEventSink::with_capacity(10);
        let opt_guard = events.deopt();
        let op = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        let node = op.complete(&mut events);
        let root = node.precede(&mut events, TestSyntaxKind::Root);
        root.complete(&mut events);
        opt_guard.complete(&mut events);
        events.assert_complete();

        let events: Vec<_> = receiver.drain().collect();
        assert_eq!(events.len(), 7);
        assert_eq!(events[0], Event::DeOpt);
        assert_eq!(
            events[1],
            Event::Enter {
                kind:        TestSyntaxKind::Operation,
                preceded_by: Some(NonZeroUsize::new(3).unwrap()),
            }
        );
        assert_eq!(
            events[4],
            Event::Enter {
                kind:        TestSyntaxKind::Root,
                preceded_by: None,
            }
        );
    }

    #[test]
    #[should_panic(expected = "cannot precede concurrent events")]
    fn precede_in_opt() {
        let (mut events, _receiver) = ConcurrentEventSink::with_capacity(10);
        let op = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        let node = op.complete(&mut events);
        let _root = node.precede(&mut events, TestSyntaxKind::Root);
    }

    #[test]
    #[should_panic(expected = "Cannot abandon in Opt")]
    fn abandon_in_opt() {
        let (mut events, _receiver) = ConcurrentEventSink::with_capacity(10);
        let _root = events.enter_node(TestSyntaxKind::Root);
        let inner = events.enter_node(TestSyntaxKind::Operation);
        events.add(Event::Token {
            kind: TestSyntaxKind::Float,
        });
        inner.abandon(&mut events);
    }
}

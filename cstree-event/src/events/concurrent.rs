use super::{EnteredNode, Event, __private::EventSinkInternal};
use crate::channel::{self, Receiver, Sender};

#[derive(Debug)]
pub struct ConcurrentEventSink<S: cstree::Syntax + 'static> {
    inner:  Vec<Event<S>>,
    sender: Sender<Event<S>>,
    deopt:  bool,
}

#[derive(Debug)]
#[repr(transparent)]
pub struct ConcurrentEventSinkRef<S: cstree::Syntax + 'static>(ConcurrentEventSink<S>);

impl<S: cstree::Syntax> ConcurrentEventSinkRef<S> {
    /// Run the given parsing function with the event sink.
    pub fn with<F, R>(self, parse: F) -> R
    where
        F: FnOnce(ConcurrentEventSink<S>) -> R,
    {
        parse(self.0)
    }
}

impl<S: cstree::Syntax> ConcurrentEventSink<S> {
    /// Create a new event sink, connected to a [`Receiver`] event source also returned from this method.
    ///
    /// This method does not return an event sink directly. Instead, it returns a reference to one that can be used by
    /// passing the parser invocation as a closure to its [`with`] method. This ensures that the channel to the
    /// [`ConcurrentEventSource`] (the [`Receiver`]) returned by this method is closed at the end of pasing and a
    /// [`TextTreeSink`] builder is notified and finishes to [`build_concurrent`].
    ///
    /// [`with`]: ConcurrentEventSinkRef::with
    /// [`ConcurrentEventSource`]: super::ConcurrentEventSource
    /// [`TextTreeSink`]: crate::parsing::TextTreeSink
    /// [`build_concurrent`]: crate::parsing::TextTreeSink::build_concurrent
    #[allow(clippy::new_ret_no_self)]
    pub fn new() -> (ConcurrentEventSinkRef<S>, Receiver<Event<S>>) {
        let (sender, receiver) = channel::unbounded_spsc();
        let this = Self {
            inner: Vec::new(),
            sender,
            deopt: false,
        };
        (ConcurrentEventSinkRef(this), receiver)
    }

    /// Create a new event sink with an internal buffer with the given `capacity`, connected to a [`Receiver`] event
    /// source also returned from this method.
    ///
    /// This method does not return an event sink directly. Instead, it returns a reference to one that can be used by
    /// passing the parser invocation as a closure to its [`with`] method. This ensures that the channel to the
    /// [`ConcurrentEventSource`] (the [`Receiver`]) returned by this method is closed at the end of pasing and a
    /// [`TextTreeSink`] builder is notified and finishes to [`build_concurrent`].
    ///
    /// [`with`]: ConcurrentEventSinkRef::with
    /// [`ConcurrentEventSource`]: super::ConcurrentEventSource
    /// [`TextTreeSink`]: crate::parsing::TextTreeSink
    /// [`build_concurrent`]: crate::parsing::TextTreeSink::build_concurrent
    pub fn with_capacity(capacity: usize) -> (ConcurrentEventSinkRef<S>, Receiver<Event<S>>) {
        let (sender, receiver) = channel::unbounded_spsc();
        let this = Self {
            inner: Vec::with_capacity(capacity),
            sender,
            deopt: false,
        };
        (ConcurrentEventSinkRef(this), receiver)
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

    #[track_caller]
    pub fn assert_complete(&self) {
        <Self as EventSinkInternal<S>>::assert_complete(self)
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
        let (events, receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            assert!(events.is_empty());
            assert!(!events.currently_deopt());
            let root = events.enter_node(TestSyntaxKind::Root);
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
            });
            root.complete(&mut events);
            assert_eq!(events.len(), 0);
            events.assert_complete();
        });

        let events: Vec<_> = receiver.drain().collect();
        assert_eq!(events.len(), 3);
    }

    #[test]
    fn discard() {
        let (events, _receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            let root = events.enter_node(TestSyntaxKind::Root);
            let opt_guard = events.deopt();
            let inner = events.enter_node(TestSyntaxKind::Operation);
            assert!(events.currently_deopt());
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
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
        });
    }

    #[test]
    fn abandon() {
        let (events, receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            let root = events.enter_node(TestSyntaxKind::Root);
            let opt_guard = events.deopt();
            let inner = events.enter_node(TestSyntaxKind::Operation);
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
            });
            inner.abandon(&mut events);
            opt_guard.complete(&mut events);
            root.complete(&mut events);
            events.assert_complete();
        });

        let events: Vec<_> = receiver.drain().collect();
        assert_eq!(events.len(), 6);
        assert_eq!(events[2], Event::Placeholder);
    }

    #[test]
    fn complete_as() {
        let (events, receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            let opt_guard = events.deopt();
            let root = events.enter_node(TestSyntaxKind::Root);
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
            });
            root.complete_as(&mut events, TestSyntaxKind::Operation);
            opt_guard.complete(&mut events);
            events.assert_complete();
        });

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
        let (events, receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            let opt_guard = events.deopt();
            let op = events.enter_node(TestSyntaxKind::Operation);
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
            });
            let node = op.complete(&mut events);
            let root = node.precede(&mut events, TestSyntaxKind::Root);
            root.complete(&mut events);
            opt_guard.complete(&mut events);
            events.assert_complete();
        });

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
        let (events, _receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            let op = events.enter_node(TestSyntaxKind::Operation);
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
            });
            let node = op.complete(&mut events);
            let _root = node.precede(&mut events, TestSyntaxKind::Root);
        });
    }

    #[test]
    #[should_panic(expected = "Cannot abandon in Opt")]
    fn abandon_in_opt() {
        let (events, _receiver) = ConcurrentEventSink::with_capacity(10);
        events.with(|mut events| {
            let _root = events.enter_node(TestSyntaxKind::Root);
            let inner = events.enter_node(TestSyntaxKind::Operation);
            events.add(Event::Token {
                kind: TestSyntaxKind::Float,
                n_input_tokens: 1,
            });
            inner.abandon(&mut events);
        });
    }
}

use super::{EnteredNode, Event, EventSink};
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

impl<S: cstree::Syntax> EventSink<S> for ConcurrentEventSink<S> {
    fn add(&mut self, event: Event<S>, _guard: super::__private::Guard) {
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

    fn into_inner(self, _guard: super::__private::Guard) -> Vec<Event<S>> {
        self.inner
    }

    fn inner(&self, _guard: super::__private::Guard) -> &Vec<Event<S>> {
        &self.inner
    }

    fn inner_mut(&mut self, _guard: super::__private::Guard) -> &mut Vec<Event<S>> {
        &mut self.inner
    }

    fn currently_deopt(&self) -> bool {
        self.deopt
    }
}

impl<S: cstree::Syntax> ConcurrentEventSink<S> {
    pub fn deopt(&mut self) -> EnteredNode {
        let idx = self.len();
        self.add(Event::DeOpt, super::__private::Guard {});
        EnteredNode::new(idx, true)
    }
}

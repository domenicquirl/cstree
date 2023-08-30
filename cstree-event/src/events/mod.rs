use core::num::NonZeroUsize;
use std::collections::VecDeque;

mod sequential;
pub use sequential::SequentialEventSink;

#[cfg(feature = "concurrent")]
mod concurrent;
#[cfg(feature = "concurrent")]
pub use concurrent::ConcurrentEventSink;

#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Event<S: cstree::Syntax> {
    Enter {
        kind:        S,
        preceded_by: Option<NonZeroUsize>,
    },
    Exit,
    Token {
        kind: S,
        n_input_tokens: usize,
    },
    #[cfg(feature = "concurrent")]
    DeOpt,
    #[cfg(feature = "concurrent")]
    Opt,
    #[doc(hidden)]
    Placeholder,
}

impl<S: cstree::Syntax> Event<S> {
    pub fn enter(kind: S) -> Self {
        Event::Enter {
            kind,
            preceded_by: None,
        }
    }
}

pub trait EventSource {
    type Syntax: cstree::Syntax;
    fn events_mut(&mut self) -> &mut [Event<Self::Syntax>];
}

impl<S: cstree::Syntax> EventSource for Vec<Event<S>> {
    type Syntax = S;

    fn events_mut(&mut self) -> &mut [Event<S>] {
        self.as_mut_slice()
    }
}

impl<S: cstree::Syntax> EventSource for VecDeque<Event<S>> {
    type Syntax = S;

    fn events_mut(&mut self) -> &mut [Event<S>] {
        self.make_contiguous()
    }
}

#[cfg(feature = "concurrent")]
pub trait ConcurrentEventSource {
    type Syntax: cstree::Syntax;

    type EventIter<'a>: Iterator<Item = Event<Self::Syntax>>
    where
        Self: 'a;

    fn is_closed(&self) -> bool;

    fn recv_event(&self) -> Option<Event<Self::Syntax>>;

    fn take_buffered_events(&self) -> Self::EventIter<'_>;
}

#[cfg(feature = "concurrent")]
impl<S: cstree::Syntax> ConcurrentEventSource for crate::channel::Receiver<Event<S>> {
    type EventIter<'a> = crate::channel::Drain<Event<S>>;
    type Syntax = S;

    fn is_closed(&self) -> bool {
        self.is_disconnected() && self.is_empty()
    }

    fn recv_event(&self) -> Option<Event<S>> {
        self.recv().ok()
    }

    fn take_buffered_events(&self) -> Self::EventIter<'_> {
        self.drain()
    }
}

mod __private {
    use super::Event;

    pub trait EventSinkInternal<S: cstree::Syntax> {
        #[doc(hidden)]
        fn add(&mut self, event: Event<S>);

        fn len(&self) -> usize;

        #[inline]
        fn is_empty(&self) -> bool {
            self.len() == 0
        }

        fn assert_complete(&self);

        #[doc(hidden)]
        fn into_inner(self) -> Vec<Event<S>>;

        #[doc(hidden)]
        fn inner(&self) -> &Vec<Event<S>>;

        #[doc(hidden)]
        fn inner_mut(&mut self) -> &mut Vec<Event<S>>;

        fn currently_deopt(&self) -> bool;
    }
}

pub trait EventSink<S: cstree::Syntax>: __private::EventSinkInternal<S> {
    // TODO(DQ): add other event variants
    fn enter_node(&mut self, kind: S) -> EnteredNode {
        let idx = self.len();
        self.add(Event::enter(kind));
        EnteredNode::new(idx, false)
    }
}
impl<S: cstree::Syntax, Sink: __private::EventSinkInternal<S>> EventSink<S> for Sink {}

#[derive(Debug)]
pub struct EnteredNode {
    idx:      usize,
    is_deopt: bool,
    is_live:  bool,
}

impl EnteredNode {
    pub(crate) fn new(idx: usize, is_deopt: bool) -> Self {
        Self {
            idx,
            is_deopt,
            is_live: true,
        }
    }

    #[inline]
    #[track_caller]
    pub fn complete<S: cstree::Syntax, Sink: EventSink<S>>(self, sink: &mut Sink) -> ExitedNode {
        self.complete_as(sink, None)
    }

    #[track_caller]
    pub fn complete_as<S: cstree::Syntax, Sink: EventSink<S>>(
        mut self,
        sink: &mut Sink,
        with_kind: Option<S>,
    ) -> ExitedNode {
        self.is_live = false;
        let is_deopt = sink.currently_deopt();
        let inner = sink.inner_mut();
        if is_deopt {
            match &mut inner[self.idx] {
                Event::Enter { kind, .. } => {
                    if let Some(with_kind) = with_kind {
                        *kind = with_kind;
                    };
                    sink.add(Event::Exit);
                }
                #[cfg(feature = "concurrent")]
                Event::DeOpt => {
                    sink.add(Event::Opt);
                }
                _ => unreachable!("entered node complete as"),
            }
        } else {
            assert!(!self.is_deopt, "Cannot `complete_as` in Opt");
            sink.add(Event::Exit);
        }
        ExitedNode { pos: self.idx }
    }

    /// Deletes the entered node and any children since.
    #[track_caller]
    pub fn discard<S: cstree::Syntax, Sink: EventSink<S>>(mut self, sink: &mut Sink) {
        let is_deopt = sink.currently_deopt();
        let inner = sink.inner_mut();

        if !is_deopt {
            panic!("Cannot discard in Opt");
        }
        #[cfg(feature = "concurrent")]
        if let Event::DeOpt = &inner[self.idx] {
            panic!("Cannot discard a DeOpt");
        }

        self.is_live = false;
        drop(inner.drain(self.idx..));
    }

    /// Mark this event to be skipped over without effect. A matching exit event is not required and the children of the
    /// entered node will become children of its parent node instead.
    #[track_caller]
    pub fn abandon<S: cstree::Syntax, Sink: EventSink<S>>(mut self, sink: &mut Sink) {
        let is_deopt = sink.currently_deopt();
        let inner = sink.inner_mut();

        if !is_deopt {
            panic!("Cannot abandon in Opt");
        }
        #[cfg(feature = "concurrent")]
        if let Event::DeOpt = &inner[self.idx] {
            panic!("Cannot abandon a DeOpt");
        }

        self.is_live = false;
        match &mut inner[self.idx] {
            e @ Event::Enter { preceded_by: None, .. } => {
                *e = Event::Placeholder;
            }
            _ => unreachable!("abandon entered node"),
        }
        if self.idx == inner.len() - 1 {
            // if we don't need to reorder the vec for this,
            // actually remove the placeholder event
            inner.pop();
        }
    }
}

impl Drop for EnteredNode {
    fn drop(&mut self) {
        if self.is_live && !::std::thread::panicking() {
            panic!("Entered Node was dropped without being completed or deleted")
        }
    }
}

#[derive(Debug)]
pub struct ExitedNode {
    pos: usize,
}

impl ExitedNode {
    #[allow(unsafe_code)]
    pub fn precede<S: cstree::Syntax, Sink: EventSink<S>>(self, sink: &mut Sink, kind: S) -> EnteredNode {
        let n = sink.enter_node(kind);
        let is_deopt = sink.currently_deopt();
        let inner = sink.inner_mut();
        assert!(is_deopt, "cannot precede concurrent events"); // Only allow precede while buffering events
        match &mut inner[self.pos] {
            Event::Enter { preceded_by, .. } => {
                // safety: since `n` is a new node, it must come after `self`
                debug_assert_ne!(n.idx - self.pos, 0);
                *preceded_by = Some(unsafe { NonZeroUsize::new_unchecked(n.idx - self.pos) });
            }
            _ => panic!("tried to precede an event that was not `Enter`"),
        }
        n
    }

    pub fn kind<S: cstree::Syntax, Sink: EventSink<S>>(&self, sink: &Sink) -> S {
        assert!(sink.currently_deopt(), "cannot access concurrent events"); // Only allow precede while buffering events
        let inner = sink.inner();
        match &inner[self.pos] {
            Event::Enter { kind, .. } => *kind,
            _ => panic!("tried to get the kind of an event that was not `Enter`"),
        }
    }
}

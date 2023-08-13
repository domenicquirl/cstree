use super::{Event, EventSink};

#[derive(Debug)]
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

impl<S: cstree::Syntax> EventSink<S> for SequentialEventSink<S> {
    #[inline]
    fn add(&mut self, event: Event<S>, _guard: super::__private::Guard) {
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
    fn into_inner(self, _guard: super::__private::Guard) -> Vec<Event<S>> {
        self.inner
    }

    #[inline]
    fn inner(&self, _guard: super::__private::Guard) -> &Vec<Event<S>> {
        &self.inner
    }

    #[inline]
    fn inner_mut(&mut self, _guard: super::__private::Guard) -> &mut Vec<Event<S>> {
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

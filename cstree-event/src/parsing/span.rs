use std::{
    fmt,
    ops::{Index, Range},
};

#[derive(Eq, PartialEq, Clone, Copy, Hash, Default, Debug)]
pub struct Span {
    /// inclusive
    pub start: u32,
    /// exclusive
    pub end:   u32,
}

impl From<Span> for Range<usize> {
    fn from(span: Span) -> Self {
        span.start as usize..span.end as usize
    }
}

impl From<Range<usize>> for Span {
    fn from(range: Range<usize>) -> Self {
        Self {
            start: range.start as u32,
            end:   range.end as u32,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl Span {
    #[inline(always)]
    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn union(self, other: Span) -> Self {
        Self {
            start: u32::min(self.start, other.start),
            end:   u32::max(self.end, other.end),
        }
    }
}

impl Index<Span> for str {
    type Output = str;

    fn index(&self, index: Span) -> &Self::Output {
        &self[Range::<usize>::from(index)]
    }
}

use std::sync::Arc;

use tlx_layout::pack::FieldLoc;

/// Native union-field scalar descriptor (`i64`, negative on missing arm):
/// - bits `16..63`: `1 + word` (payload word offset in union `[tag, payload...]`, always `>= 1`)
/// - bits `8..16`: right-shift `0..=63` (`0` for whole word)
/// - bits `0..8`: right-trim `64 - bits` (`0` for whole word, `1..=63` for packed bitfield)
pub(crate) const UNION_DESC_MISSING: i64 = -1;
pub(crate) const UNION_DESC_WORD_SHIFT: u32 = 16;
pub(crate) const UNION_DESC_BIT_SHIFT: u32 = 8;
pub(crate) const UNION_DESC_FIELD_MASK: i64 = 63;

/// Encode a union arm's field location into a native descriptor (`None` if the
/// payload word offset exceeds the 47-bit signed descriptor field).
pub(crate) fn union_loc_desc(loc: Option<FieldLoc>) -> Option<i64> {
    let max_word = ((i64::MAX >> UNION_DESC_WORD_SHIFT) - 1) as usize;
    match loc {
        None => Some(UNION_DESC_MISSING),
        Some(FieldLoc::Words(w)) => (w <= max_word).then(|| ((1 + w) as i64) << UNION_DESC_WORD_SHIFT),
        Some(FieldLoc::Bits(pos)) => (pos.word <= max_word && pos.bits >= 1 && pos.bits <= 63 && pos.shift < 64).then(|| {
            (((1 + pos.word) as i64) << UNION_DESC_WORD_SHIFT) | ((pos.shift as i64) << UNION_DESC_BIT_SHIFT) | ((64 - pos.bits) as i64)
        }),
    }
}

#[cfg(test)]
pub(crate) fn rank(radices: &[u64], words: &[u64]) -> u64 {
    rank_with(&radices[..radices.len().min(words.len())], |index| words[index])
}

pub(crate) fn rank_with(radices: &[u64], mut word: impl FnMut(usize) -> u64) -> u64 {
    radices.iter().enumerate().fold(0, |acc, (index, radix)| acc * radix + word(index))
}

pub(crate) struct UnionArms<'a> {
    arms: std::slice::Iter<'a, Arc<[u64]>>,
    base: u64,
}

impl<'a> UnionArms<'a> {
    pub(crate) fn new(arms: &'a [Arc<[u64]>]) -> Self {
        Self { arms: arms.iter(), base: 0 }
    }

    #[cfg(test)]
    pub(crate) fn total(mut self) -> u64 {
        for _ in self.by_ref() {}
        self.base
    }
}

impl<'a> Iterator for UnionArms<'a> {
    type Item = (u64, &'a [u64]);

    fn next(&mut self) -> Option<Self::Item> {
        let radices = self.arms.next()?;
        let base = self.base;
        self.base += radices.iter().product::<u64>();
        Some((base, radices))
    }
}

pub(crate) struct RecodeTable<'a> {
    pub(crate) arm_base: &'a [u64],
    pub(crate) table: &'a [u64],
    pub(crate) words: usize,
}

impl<'a> RecodeTable<'a> {
    pub(crate) fn codes(&self) -> usize {
        self.table.len() / self.words.max(1)
    }

    pub(crate) fn lookup(&self, mut word: impl FnMut(usize) -> u64) -> Option<&'a [u64]> {
        let first = word(0);
        let code = if self.arm_base.is_empty() { first } else { self.arm_base.get(first as usize)?.wrapping_add(word(1)) };
        let start = usize::try_from(code).ok()?.checked_mul(self.words)?;
        self.table.get(start..start.checked_add(self.words)?).filter(|entry| entry[0] != u64::MAX)
    }
}

#[cfg(test)]
#[path = "encoding_tests.rs"]
mod tests;

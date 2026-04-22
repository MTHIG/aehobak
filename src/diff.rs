/*-
 * Copyright 2025 David Michael Barr
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted providing that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

use crate::control::Aehobak;
use crate::encode::EncoderState;
use anyhow::{ensure, Context, Error, Result};
use std::io;
use std::io::Write;

/// Directly generate a compact representation of bsdiff output.
/// If numeric limits are reached, the error will be wrapped with `io::Error`.
pub fn diff<T: Write>(old: &[u8], new: &[u8], writer: &mut T) -> io::Result<()> {
    match diff_internal(old, new, writer) {
        Ok(_) => Ok(()),
        Err(e) => match e.downcast::<io::Error>() {
            Ok(e) => Err(e),
            Err(e) => Err(io::Error::other(e)),
        },
    }
}

fn diff_internal(old: &[u8], new: &[u8], writer: &mut dyn Write) -> Result<()> {
    #[cfg(miri)]
    let sa = suf_sort_naive(old)?;
    #[cfg(not(miri))]
    let sa = sais(old)?;
    let mut scanner = ScanState::new(old, new, &sa);
    let mut encoder = EncoderState::new(new.len());

    while !scanner.done() {
        if !scanner.advance() {
            continue;
        }
        let (add, back) = scanner.optimize_overlap(scanner.calc_add(), scanner.calc_back());
        let (copy, seek) = scanner.calc_copy_seek(add, back);

        let add_u32: u32 = add.try_into()?;
        let copy_u32: u32 = copy.try_into()?;
        let seek_i32: i32 = seek.try_into()?;

        encoder.control(Aehobak {
            add: add_u32,
            copy: copy_u32,
            seek: seek_i32,
        });
        encoder.add(scanner.old_add_slice(add)?, scanner.new_add_slice(add)?);
        encoder.copy(scanner.new_copy_slice(add, copy)?);
        scanner.commit(back)?;
    }
    encoder.finalize(writer)?;
    Ok(())
}

#[cfg(all(
    not(miri),
    not(feature = "divsufsort"),
    not(feature = "cdivsufsort"),
    not(feature = "divsufsort-rs")
))]
compile_error!(
    "Either feature \"divsufsort\", \"cdivsufsort\", or \"divsufsort-rs\" must be enabled."
);

#[cfg(miri)]
fn suf_sort_naive(old: &[u8]) -> Result<Box<[u32]>> {
    ensure!(old.len() <= i32::MAX as usize, "input too large");
    let mut sa: Vec<u32> = (0..old.len() as u32).collect();
    sa.sort_unstable_by_key(|&v| {
        // SAFETY: Values of `sa` are offsets into `old`
        unsafe { old.get_unchecked(v as usize..) }
    });
    Ok(sa.into_boxed_slice())
}

#[cfg(not(miri))]
fn sais(old: &[u8]) -> Result<Box<[u32]>> {
    ensure!(old.len() <= i32::MAX as usize, "input too large");
    #[cfg(feature = "divsufsort")]
    let (_, sa) = divsufsort::sort(old).into_parts();
    #[cfg(all(not(feature = "divsufsort"), feature = "cdivsufsort"))]
    let (_, sa) = cdivsufsort::sort(old).into_parts();
    #[cfg(all(
        not(feature = "divsufsort"),
        not(feature = "cdivsufsort"),
        feature = "divsufsort-rs"
    ))]
    let sa = {
        let mut sa = vec![0i32; old.len()];
        divsufsort_rs::divsufsort(old, &mut sa).map_err(|e| anyhow::anyhow!("{:?}", e))?;
        sa
    };
    // SAFETY: i32 to u32 transmute is safe; non-negative values
    let sa: Vec<u32> = unsafe { core::mem::transmute(sa) };
    Ok(sa.into_boxed_slice())
}

#[inline(never)]
fn mismatch(old: &[u8], new: &[u8]) -> usize {
    let min_len = old.len().min(new.len()).min(i32::MAX as usize);
    let mut i = 0;
    while i + 32 <= min_len {
        if old[i..i + 32] != new[i..i + 32] {
            break;
        }
        i += 32;
    }
    while i < min_len {
        if old[i] != new[i] {
            break;
        }
        i += 1;
    }
    i
}

const SMALL_MATCH: usize = 12;
const MISMATCH_THRESHOLD: usize = 8;
const LONG_SUFFIX: usize = 256;

struct ScanState<'a> {
    sa: &'a [u32],
    old: &'a [u8],
    new: &'a [u8],
    scan: usize,
    len: usize,
    pos: usize,
    last_scan: usize,
    last_pos: usize,
    last_offset: isize,
}

impl<'a> ScanState<'a> {
    #[inline(always)]
    fn new(old: &'a [u8], new: &'a [u8], sa: &'a [u32]) -> Self {
        Self {
            sa,
            old,
            new,
            scan: 0,
            len: 0,
            pos: 0,
            last_scan: 0,
            last_pos: 0,
            last_offset: 0,
        }
    }

    #[inline(always)]
    fn done(&self) -> bool {
        self.scan >= self.new.len()
    }

    #[inline(always)]
    fn match_is_redundant(len: usize, similar: usize) -> bool {
        similar == len || len <= SMALL_MATCH || len <= similar + MISMATCH_THRESHOLD
    }

    fn find_best_match(&self) -> (usize, usize) {
        self.find_best_match_at(self.scan)
    }

    fn find_best_match_at(&self, scan: usize) -> (usize, usize) {
        let mut sa = self.sa;
        // SAFETY: callers ensure `scan <= new.len()`
        let new = unsafe { self.new.get_unchecked(scan..) };

        while sa.len() > 2 {
            let pos = (sa.len() - 1) / 2;
            // SAFETY: pos indexes sa
            let old_start = unsafe { *sa.get_unchecked(pos) as usize };
            // SAFETY: content of sa indexes old
            let old_slice = unsafe { self.old.get_unchecked(old_start..) };

            let len = old_slice.len().min(new.len());
            sa = if old_slice.get(..len) < new.get(..len) {
                &sa[pos..]
            } else {
                &sa[..=pos]
            };
        }

        if sa.is_empty() {
            return (self.sa.len(), 0);
        }
        // SAFETY: sa is not empty
        let (a_start, b_start) = unsafe {
            (
                *sa.first().unwrap_unchecked() as usize,
                *sa.last().unwrap_unchecked() as usize,
            )
        };
        // SAFETY: content of sa indexes old
        let (a_slice, b_slice) = unsafe {
            (
                self.old.get_unchecked(a_start..),
                self.old.get_unchecked(b_start..),
            )
        };
        let a = mismatch(a_slice, new);
        let b = mismatch(b_slice, new);

        if a > b {
            (a_start, a)
        } else {
            (b_start, b)
        }
    }

    #[inline(always)]
    fn advance_scan(&mut self, step: usize, score: &mut usize) {
        for idx in self.scan..self.scan.saturating_add(step).min(self.new.len()) {
            let old_idx = idx.wrapping_add_signed(self.last_offset);
            if old_idx < self.old.len() && self.old[old_idx] == self.new[idx] {
                *score = score.saturating_sub(1);
            }
        }
        self.scan += step;
    }

    #[inline(always)]
    fn similar_suffix_match(
        &self,
        prev_scan: usize,
        prev_pos: usize,
        prev_len: usize,
        scan: usize,
        len: usize,
    ) -> usize {
        let delta = match scan.checked_sub(prev_scan) {
            Some(delta) if delta < prev_len => delta,
            _ => return 0,
        };
        let old_start = match prev_pos.checked_add(delta) {
            Some(old_start) if old_start < self.old.len() => old_start,
            _ => return 0,
        };
        mismatch(unsafe { self.old.get_unchecked(old_start..) }, unsafe {
            self.new.get_unchecked(scan..)
        })
        .min(len)
    }

    #[inline(always)]
    fn binary_search_suffix_skip(
        &self,
        prev_scan: usize,
        prev_pos: usize,
        prev_len: usize,
        scan: usize,
        len: usize,
        similar: usize,
    ) -> usize {
        if len <= LONG_SUFFIX || similar <= len {
            return len;
        }

        let max_step = similar.min(self.new.len().saturating_sub(scan));
        let mut best = len;
        let mut low = len;
        let mut high = max_step;

        while low <= high {
            let mid = low + (high - low) / 2;
            let future_scan = scan + mid;
            if future_scan >= self.new.len() {
                high = mid.saturating_sub(1);
                continue;
            }

            let (_future_pos, future_len) = self.find_best_match_at(future_scan);
            let future_similar =
                self.similar_suffix_match(prev_scan, prev_pos, prev_len, future_scan, future_len);

            if future_len != 0 && Self::match_is_redundant(future_len, future_similar) {
                best = mid;
                low = mid + 1;
            } else {
                high = mid.saturating_sub(1);
            }
        }

        best
    }

    #[inline(never)]
    fn advance(&mut self) -> bool {
        debug_assert!(self.scan <= self.new.len());
        debug_assert!(self.len <= self.new.len().saturating_sub(self.scan));
        self.scan += self.len;
        let mut score = 0;
        let mut subscan = self.scan;
        let mut prev_match = None;

        while self.scan < self.new.len() {
            (self.pos, self.len) = self.find_best_match();
            debug_assert!(self.len <= self.new.len().saturating_sub(self.scan));
            let scan_limit = self.scan + self.len;

            while subscan < scan_limit {
                let idx = subscan.wrapping_add_signed(self.last_offset);
                if idx < self.old.len() && self.old[idx] == self.new[subscan] {
                    score += 1;
                }
                subscan += 1;
            }

            if self.len == 0 {
                prev_match = None;
                self.advance_scan(1, &mut score);
                continue;
            }

            if let Some((prev_scan, prev_pos, prev_len)) = prev_match {
                let similar =
                    self.similar_suffix_match(prev_scan, prev_pos, prev_len, self.scan, self.len);
                if Self::match_is_redundant(self.len, similar) {
                    prev_match = Some((self.scan, self.pos, self.len));
                    let step = self.binary_search_suffix_skip(
                        prev_scan, prev_pos, prev_len, self.scan, self.len, similar,
                    );
                    self.advance_scan(step, &mut score);
                    continue;
                }
            }

            if (self.len == score && self.len != 0) || self.len > score + 8 {
                break;
            }

            prev_match = Some((self.scan, self.pos, self.len));
            self.advance_scan(1, &mut score);
        }
        self.len != score || self.scan == self.new.len()
    }

    fn calc_add(&self) -> usize {
        let mut add = 0;
        let mut score = 0;
        let mut best = 0;
        let mut i = 0;

        debug_assert!(self.last_scan <= self.scan);
        while self.last_scan + i < self.scan && self.last_pos + i < self.old.len() {
            if self
                .old
                .get(self.last_pos + i)
                .zip(self.new.get(self.last_scan + i))
                .is_some_and(|(o, n)| o == n)
            {
                score += 1;
            }
            i += 1;
            if score * 2 - i as i32 > best * 2 - add as i32 {
                best = score;
                add = i;
            }
        }
        add
    }

    fn calc_back(&self) -> usize {
        if self.scan >= self.new.len() {
            return 0;
        }

        let mut back = 0;
        let mut score = 0;
        let mut best = 0;
        let mut i = 1;

        while self.scan >= self.last_scan + i && self.pos >= i {
            if self
                .old
                .get(self.pos - i)
                .zip(self.new.get(self.scan - i))
                .is_some_and(|(o, n)| o == n)
            {
                score += 1;
            }

            if score * 2 - i as isize > best * 2 - back as isize {
                best = score;
                back = i;
            }
            i += 1;
        }
        back
    }

    fn optimize_overlap(&self, mut add: usize, mut back: usize) -> (usize, usize) {
        debug_assert!(self.scan >= back);
        if self.last_scan + add > self.scan - back {
            let overlap = self.last_scan + add - (self.scan - back);

            let mut score = 0;
            let mut best = 0;
            let mut forward = 0;

            for i in 0..overlap {
                // Safely compare indices within bounds
                if self.new.get(self.last_scan + add - overlap + i)
                    == self.old.get(self.last_pos + add - overlap + i)
                {
                    score += 1;
                }

                if self.new.get(self.scan - back + i) == self.old.get(self.pos - back + i) {
                    score -= 1;
                }

                if score > best {
                    best = score;
                    forward = i + 1;
                }
            }

            add = add + forward - overlap;
            back -= forward;
        }

        (add, back)
    }

    fn calc_copy_seek(&self, add: usize, back: usize) -> (usize, isize) {
        let copy = self.scan - back - (self.last_scan + add);
        let seek = (self.pos as isize) - (self.last_pos as isize) - ((back + add) as isize);
        (copy, seek)
    }

    #[inline(always)]
    fn old_add_slice(&self, add: usize) -> Result<&[u8], Error> {
        self.old
            .get(self.last_pos..)
            .and_then(|s| s.get(..add))
            .context("")
    }

    #[inline(always)]
    fn new_add_slice(&self, add: usize) -> Result<&[u8], Error> {
        self.new
            .get(self.last_scan..)
            .and_then(|s| s.get(..add))
            .context("")
    }

    #[inline(always)]
    fn new_copy_slice(&self, add: usize, copy: usize) -> Result<&[u8], Error> {
        self.new
            .get(self.last_scan..)
            .and_then(|s| s.get(add..))
            .and_then(|s| s.get(..copy))
            .context("")
    }

    fn commit(&mut self, back: usize) -> Result<()> {
        self.last_scan = self.scan.checked_sub(back).context("")?;
        self.last_pos = self.pos.checked_sub(back).context("")?;
        self.last_offset = (self.pos as isize)
            .checked_sub(self.scan as isize)
            .context("")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{ScanState, LONG_SUFFIX};

    fn naive_sa(old: &[u8]) -> Box<[u32]> {
        let mut sa: Vec<u32> = (0..old.len() as u32).collect();
        sa.sort_unstable_by_key(|&v| &old[v as usize..]);
        sa.into_boxed_slice()
    }

    #[test]
    fn repeated_suffix_matches_are_classified_as_redundant() {
        let old = b"abcabcabcabcabcabc";
        let new = b"xabcabcabcabcabcabcy";
        let sa = naive_sa(old);
        let scanner = ScanState::new(old, new, &sa);

        let similar = scanner.similar_suffix_match(1, 0, old.len(), 4, old.len() - 3);

        assert_eq!(similar, old.len() - 3);
    }

    #[test]
    fn long_suffix_binary_search_skip_never_regresses_below_current_match() {
        let old = vec![0u8; 4096];
        let mut new = vec![1u8];
        new.extend(std::iter::repeat_n(0u8, 3072));
        new.push(2);

        let sa = naive_sa(&old);
        let scanner = ScanState::new(&old, &new, &sa);
        let scan = 1;
        let len = LONG_SUFFIX + 1;
        let similar = scanner.similar_suffix_match(0, 0, old.len(), scan, new.len() - scan);
        let step = scanner.binary_search_suffix_skip(0, 0, old.len(), scan, len, similar);

        assert!(similar > len);
        assert!(step > len);
    }
}

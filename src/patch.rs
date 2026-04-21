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

use std::hint::assert_unchecked;
use std::io;
use std::io::ErrorKind::{InvalidData, UnexpectedEof};
use std::iter::zip;
use streamvbyte64::{Coder, Coder0124};

/// Directly apply a compact representation of bsdiff output.
/// Attempts to fill `new` beyond its capacity will result in `Err`.
#[allow(clippy::ptr_arg)]
pub fn patch(old: &[u8], patch: &[u8], new: &mut Vec<u8>) -> io::Result<()> {
    let coder = Coder0124::new();
    let (prefix_tag, patch) = patch.split_at_checked(1).ok_or(UnexpectedEof)?;
    let prefix_len = coder.data_len(prefix_tag);
    let (prefix_data, patch) = patch.split_at_checked(prefix_len).ok_or(UnexpectedEof)?;
    let (deltas_len, literals_len, controls, data_len) = {
        let mut v = [0u32; 4];
        coder.decode(prefix_tag, prefix_data, &mut v);
        (v[0] as usize, v[1] as usize, v[2] as usize, v[3] as usize)
    };

    let (mut delta_diffs, patch) = patch.split_at_checked(deltas_len).ok_or(UnexpectedEof)?;
    let (mut literals, patch) = patch.split_at_checked(literals_len).ok_or(UnexpectedEof)?;

    // `controls` and `deltas_len` are length of data before streamvbyte
    // div by 4 to get number of tags (u8)
    let controls_div_4 = controls.div_ceil(4);
    let deltas_div_4 = deltas_len.div_ceil(4);
    let tags_len = controls_div_4
        .checked_mul(3)
        .ok_or(io::Error::from(InvalidData))?
        .checked_add(deltas_div_4)
        .ok_or(io::Error::from(InvalidData))?;
    let u32_seq_len = tags_len
        .checked_mul(4)
        .ok_or(io::Error::from(InvalidData))?;
    // SAFETY: This follows from the checked arithmetic above
    debug_assert!(u32_seq_len >= controls_div_4 * 12);
    unsafe { assert_unchecked(u32_seq_len >= controls_div_4 * 12) }

    let (tags, patch) = patch.split_at_checked(tags_len).ok_or(UnexpectedEof)?;
    let (copy_tags, tags) = tags.split_at_checked(controls_div_4).ok_or(InvalidData)?;
    let (mut delta_tags, tags) = tags.split_at_checked(deltas_div_4).ok_or(InvalidData)?;
    let (seek_tags, add_tags) = tags.split_at_checked(controls_div_4).ok_or(InvalidData)?;

    let copy_data_len = coder.data_len(copy_tags);
    let delta_data_len = coder.data_len(delta_tags);
    let seek_data_len = coder.data_len(seek_tags);
    let add_data_len = coder.data_len(add_tags);
    if add_data_len
        .checked_add(copy_data_len)
        .and_then(|x| x.checked_add(delta_data_len))
        .and_then(|x| x.checked_add(seek_data_len))
        .ok_or(InvalidData)?
        > data_len
    {
        return Err(io::Error::from(UnexpectedEof));
    }
    let (data, _) = patch.split_at_checked(data_len).ok_or(UnexpectedEof)?;
    let (mut copy_data, data) = data.split_at_checked(copy_data_len).ok_or(InvalidData)?;
    let (mut delta_data, data) = data.split_at_checked(delta_data_len).ok_or(InvalidData)?;
    let (mut seek_data, mut add_data) = data.split_at_checked(seek_data_len).ok_or(InvalidData)?;

    let mut old_cursor: usize = 0;
    let mut copy_cursor: usize = 0;

    let mut delta_pos_buf = [0; 32];
    let mut delta_pos = &mut delta_pos_buf[..0];
    let mut delta_base = 0;

    for (add_tags, (copy_tags, seek_tags)) in zip(
        add_tags.chunks(8),
        zip(copy_tags.chunks(8), seek_tags.chunks(8)),
    ) {
        let mut adds = [0; 32];
        let mut copies = [0; 32];
        let mut seeks = [0; 32];
        {
            let mut window = [0; 8];
            let read = coder.decode(pad8(&mut window, add_tags), add_data, &mut adds);
            // SAFETY: This follows from the checked arithmetic above
            debug_assert!(read <= add_data.len());
            unsafe { assert_unchecked(read <= add_data.len()) }
            add_data = &add_data[read..];
        }
        {
            let mut window = [0; 8];
            let read = coder.decode(pad8(&mut window, copy_tags), copy_data, &mut copies);
            // SAFETY: This follows from the checked arithmetic above
            debug_assert!(read <= copy_data.len());
            unsafe { assert_unchecked(read <= copy_data.len()) }
            copy_data = &copy_data[read..];
        }
        {
            let mut window = [0; 8];
            let read = coder.decode(pad8(&mut window, seek_tags), seek_data, &mut seeks);
            // SAFETY: This follows from the checked arithmetic above
            debug_assert!(read <= seek_data.len());
            unsafe { assert_unchecked(read <= seek_data.len()) }
            seek_data = &seek_data[read..];
        }
        for seek in &mut seeks {
            let x = *seek;
            *seek = (x >> 1) ^ (x & 1).wrapping_neg()
        }
        for (&add, (&copy, &seek)) in zip(&adds, zip(&copies, &seeks)) {
            let (add, copy, seek) = (add as usize, copy as usize, seek as i32 as isize);
            if new
                .len()
                .checked_add(add)
                .ok_or(io::Error::from(InvalidData))?
                > new.capacity()
            {
                return Err(io::Error::from(UnexpectedEof));
            }
            let old_cursor_add = old_cursor
                .checked_add(add)
                .ok_or(io::Error::from(InvalidData))?;
            new.extend_from_slice(
                old.get(old_cursor..old_cursor_add)
                    .ok_or(io::Error::from(UnexpectedEof))?,
            );
            'outer: while !delta_diffs.is_empty() {
                if delta_pos.is_empty() {
                    let mut window = [0; 8];
                    let current = if delta_tags.len() >= 8 {
                        let (to_decode, delta_tags_rest) =
                            delta_tags.split_at_checked(8).ok_or(UnexpectedEof)?;
                        delta_tags = delta_tags_rest;
                        to_decode
                    } else {
                        window[..delta_tags.len()].copy_from_slice(delta_tags);
                        delta_tags = &delta_tags[delta_tags.len()..];
                        &window[..]
                    };
                    let read =
                        coder.decode_deltas(delta_base, current, delta_data, &mut delta_pos_buf);
                    // SAFETY: This follows from the checked arithmetic above
                    debug_assert!(read <= delta_data.len());
                    unsafe { assert_unchecked(read <= delta_data.len()) }
                    for (idx, pos) in delta_pos_buf.iter_mut().enumerate() {
                        *pos = (*pos).wrapping_add(idx as u32);
                    }
                    delta_base = {
                        let [.., last] = delta_pos_buf;
                        last + 1
                    };
                    delta_pos = &mut delta_pos_buf[..]; // whole buffer
                    delta_data = &delta_data[read..];
                }
                let nonzero = delta_diffs.len().min(delta_pos.len());
                for i in 0..nonzero {
                    let delta_cursor = copy_cursor.wrapping_add(delta_pos[i] as usize);
                    if delta_cursor >= new.len() {
                        delta_pos = &mut delta_pos[i..]; // remaining positions
                        delta_diffs = &delta_diffs[i..];
                        break 'outer;
                    }
                    new[delta_cursor] = new[delta_cursor].wrapping_add(delta_diffs[i]);
                }
                delta_pos = &mut delta_pos[nonzero..]; // remaining positions
                delta_diffs = &delta_diffs[nonzero..];
            }
            if new
                .len()
                .checked_add(copy)
                .ok_or(io::Error::from(InvalidData))?
                > new.capacity()
            {
                Err(io::Error::from(UnexpectedEof))?;
            }
            literals = {
                let (to_extend, literals_rest) = literals
                    .split_at_checked(copy)
                    .ok_or(io::Error::from(UnexpectedEof))?;
                new.extend_from_slice(to_extend);
                literals_rest
            };
            copy_cursor = copy_cursor.wrapping_add(copy);
            old_cursor = (old_cursor_add as isize)
                .checked_add(seek)
                .ok_or(io::Error::from(InvalidData))? as usize;
        }
    }
    Ok(())
}

#[inline(always)]
fn pad8<'a>(window: &'a mut [u8; 8], add_tags: &'a [u8]) -> &'a [u8] {
    if add_tags.len() >= 8 {
        add_tags
    } else {
        *window = [0; 8];
        window[..add_tags.len()].copy_from_slice(add_tags);
        window
    }
}

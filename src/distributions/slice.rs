// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use core::num::NonZeroUsize;

use crate::distributions::{Distribution, Uniform};
#[cfg(feature = "alloc")]
use alloc::string::String;

/// A distribution to sample items uniformly from a slice.
///
/// [`Slice::new`] constructs a distribution referencing a slice and uniformly
/// samples references from the items in the slice. It may do extra work up
/// front to make sampling of multiple values faster; if only one sample from
/// the slice is required, [`IndexedRandom::choose`] can be more efficient.
///
/// Steps are taken to avoid bias which might be present in naive
/// implementations; for example `slice[rng.gen() % slice.len()]` samples from
/// the slice, but may be more likely to select numbers in the low range than
/// other values.
///
/// This distribution samples with replacement; each sample is independent.
/// Sampling without replacement requires state to be retained, and therefore
/// cannot be handled by a distribution; you should instead consider methods
/// on [`IndexedRandom`], such as [`IndexedRandom::choose_multiple`].
///
/// # Example
///
/// ```
/// use rand::Rng;
/// use rand::distributions::Slice;
///
/// let vowels = ['a', 'e', 'i', 'o', 'u'];
/// let vowels_dist = Slice::new(&vowels).unwrap();
/// let rng = rand::thread_rng();
///
/// // build a string of 10 vowels
/// let vowel_string: String = rng
///     .sample_iter(&vowels_dist)
///     .take(10)
///     .collect();
///
/// println!("{}", vowel_string);
/// assert_eq!(vowel_string.len(), 10);
/// assert!(vowel_string.chars().all(|c| vowels.contains(&c)));
/// ```
///
/// For a single sample, [`IndexedRandom::choose`][crate::seq::IndexedRandom::choose]
/// may be preferred:
///
/// ```
/// use rand::seq::IndexedRandom;
///
/// let vowels = ['a', 'e', 'i', 'o', 'u'];
/// let mut rng = rand::thread_rng();
///
/// println!("{}", vowels.choose(&mut rng).unwrap())
/// ```
///
/// [`IndexedRandom`]: crate::seq::IndexedRandom
/// [`IndexedRandom::choose`]: crate::seq::IndexedRandom::choose
/// [`IndexedRandom::choose_multiple`]: crate::seq::IndexedRandom::choose_multiple
#[derive(Debug, Clone, Copy)]
pub struct Slice<'a, T> {
    slice: &'a [T],
    range: Uniform<usize>,
    num_choices: NonZeroUsize,
}

impl<'a, T> Slice<'a, T> {
    /// Create a new `Slice` instance which samples uniformly from the slice.
    /// Returns `Err` if the slice is empty.
    pub fn new(slice: &'a [T]) -> Result<Self, EmptySlice> {
        let num_choices = NonZeroUsize::new(slice.len()).ok_or(EmptySlice)?;

        Ok(Self {
            slice,
            range: Uniform::new(0, num_choices.get()).unwrap(),
            num_choices,
        })
    }

    /// Returns the count of choices in this distribution
    pub fn num_choices(&self) -> NonZeroUsize {
        self.num_choices
    }
}

impl<'a, T> Distribution<&'a T> for Slice<'a, T> {
    fn sample<R: crate::Rng + ?Sized>(&self, rng: &mut R) -> &'a T {
        let idx = self.range.sample(rng);

        debug_assert!(
            idx < self.slice.len(),
            "Uniform::new(0, {}) somehow returned {}",
            self.slice.len(),
            idx
        );

        // Safety: at construction time, it was ensured that the slice was
        // non-empty, and that the `Uniform` range produces values in range
        // for the slice
        unsafe { self.slice.get_unchecked(idx) }
    }
}

/// Error type indicating that a [`Slice`] distribution was improperly
/// constructed with an empty slice.
#[derive(Debug, Clone, Copy)]
pub struct EmptySlice;

impl core::fmt::Display for EmptySlice {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "Tried to create a `distributions::Slice` with an empty slice"
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for EmptySlice {}

/// Note: the `String` is potentially left with excess capacity; optionally the
/// user may call `string.shrink_to_fit()` afterwards.
#[cfg(feature = "alloc")]
#[cfg_attr(doc_cfg, doc(cfg(feature = "alloc")))]
impl<'a> super::DistString for Slice<'a, char> {
    fn append_string<R: crate::Rng + ?Sized>(&self, rng: &mut R, string: &mut String, len: usize) {
        // Get the max char length to minimize extra space.
        // Limit this check to avoid searching for long slice.
        let max_char_len = if self.slice.len() < 200 {
            self.slice
                .iter()
                .try_fold(1, |max_len, char| {
                    // When the current max_len is 4, the result max_char_len will be 4.
                    Some(max_len.max(char.len_utf8())).filter(|len| *len < 4)
                })
                .unwrap_or(4)
        } else {
            4
        };

        // Split the extension of string to reuse the unused capacities.
        // Skip the split for small length or only ascii slice.
        let mut extend_len = if max_char_len == 1 || len < 100 { len } else { len / 4 };
        let mut remain_len = len;
        while extend_len > 0 {
            string.reserve(max_char_len * extend_len);
            string.extend(self.sample_iter(&mut *rng).take(extend_len));
            remain_len -= extend_len;
            extend_len = extend_len.min(remain_len);
        }
    }
}

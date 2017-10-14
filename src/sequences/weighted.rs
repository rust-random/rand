// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Weighted choices
//! 
//! TODO: evaluate whether this functionality should be stabilised as-is,
//! adapted, or removed entirely.

use Rng;
use distributions::Distribution;
use distributions::range::{Range, RangeInt};

/// A value with a particular weight for use with `WeightedChoice`.
#[derive(Copy, Clone, Debug)]
pub struct Weighted<T> {
    /// The numerical weight of this item
    pub weight: u32,
    /// The actual item which is being weighted
    pub item: T,
}

/// A distribution that selects from a finite collection of weighted items.
///
/// Each item has an associated weight that influences how likely it
/// is to be chosen: higher weight is more likely.
///
/// # Example
///
/// ```rust
/// use rand::distributions::Distribution;
/// use rand::sequences::{Weighted, WeightedChoice};
///
/// let items = vec!(Weighted { weight: 2, item: 'a' },
///                      Weighted { weight: 4, item: 'b' },
///                      Weighted { weight: 1, item: 'c' });
/// let wc = WeightedChoice::new(items);
/// let mut rng = rand::thread_rng();
/// for _ in 0..16 {
///      // on average prints 'a' 4 times, 'b' 8 and 'c' twice.
///      println!("{}", wc.sample(&mut rng));
/// }
/// ```
#[derive(Clone, Debug)]
pub struct WeightedChoice<T: Clone> {
    items: Vec<Weighted<T>>,
    weight_range: Range<RangeInt<u32>>,
}

impl<T: Clone> WeightedChoice<T> {
    /// Create a new `WeightedChoice`.
    ///
    /// Panics if:
    /// - `v` is empty
    /// - the total weight is 0
    /// - the total weight is larger than a `u32` can contain.
    pub fn new(mut items: Vec<Weighted<T>>) -> WeightedChoice<T> {
        // strictly speaking, this is subsumed by the total weight == 0 case
        assert!(!items.is_empty(), "WeightedChoice::new called with no items");

        let mut running_total: u32 = 0;

        // we convert the list from individual weights to cumulative
        // weights so we can binary search. This *could* drop elements
        // with weight == 0 as an optimisation.
        for ref mut item in items.iter_mut() {
            running_total = match running_total.checked_add(item.weight) {
                Some(n) => n,
                None => panic!("WeightedChoice::new called with a total weight \
                               larger than a u32 can contain")
            };

            item.weight = running_total;
        }
        assert!(running_total != 0, "WeightedChoice::new called with a total weight of 0");

        WeightedChoice {
            items: items,
            // we're likely to be generating numbers in this range
            // relatively often, so might as well cache it
            weight_range: Range::new(0, running_total)
        }
    }
}

impl<T: Clone> Distribution<T> for WeightedChoice<T> {
    fn sample<R: Rng+?Sized>(&self, rng: &mut R) -> T {
        // we want to find the first element that has cumulative
        // weight > sample_weight, which we do by binary since the
        // cumulative weights of self.items are sorted.

        // choose a weight in [0, total_weight)
        let sample_weight = self.weight_range.sample(rng);

        // short circuit when it's the first item
        if sample_weight < self.items[0].weight {
            return self.items[0].item.clone();
        }

        let mut idx = 0;
        let mut modifier = self.items.len();

        // now we know that every possibility has an element to the
        // left, so we can just search for the last element that has
        // cumulative weight <= sample_weight, then the next one will
        // be "it". (Note that this greatest element will never be the
        // last element of the vector, since sample_weight is chosen
        // in [0, total_weight) and the cumulative weight of the last
        // one is exactly the total weight.)
        while modifier > 1 {
            let i = idx + modifier / 2;
            if self.items[i].weight <= sample_weight {
                // we're small, so look to the right, but allow this
                // exact element still.
                idx = i;
                // we need the `/ 2` to round up otherwise we'll drop
                // the trailing elements when `modifier` is odd.
                modifier += 1;
            } else {
                // otherwise we're too big, so go left. (i.e. do
                // nothing)
            }
            modifier /= 2;
        }
        return self.items[idx + 1].item.clone();
    }
}

#[cfg(test)]
mod tests {
    use rand_core::mock::MockAddRng;
    use distributions::Distribution;
    use super::{WeightedChoice, Weighted};

    #[test]
    fn test_weighted_choice() {
        // this makes assumptions about the internal implementation of
        // WeightedChoice, specifically: it doesn't reorder the items,
        // it doesn't do weird things to the RNG (so 0 maps to 0, 1 to
        // 1, internally; modulo a modulo operation).

        macro_rules! t {
            ($items:expr, $expected:expr) => {{
                let items = $items;
                let wc = WeightedChoice::new(items);
                let expected = $expected;

                let mut rng = MockAddRng::new(0u32, 1);

                for &val in expected.iter() {
                    assert_eq!(wc.sample(&mut rng), val)
                }
            }}
        }

        t!(vec!(Weighted { weight: 1, item: 10}), [10]);

        // skip some
        t!(vec!(Weighted { weight: 0, item: 20},
                Weighted { weight: 2, item: 21},
                Weighted { weight: 0, item: 22},
                Weighted { weight: 1, item: 23}),
           [21,21, 23]);

        // different weights
        t!(vec!(Weighted { weight: 4, item: 30},
                Weighted { weight: 3, item: 31}),
           [30,30,30,30, 31,31,31]);

        // check that we're binary searching
        // correctly with some vectors of odd
        // length.
        t!(vec!(Weighted { weight: 1, item: 40},
                Weighted { weight: 1, item: 41},
                Weighted { weight: 1, item: 42},
                Weighted { weight: 1, item: 43},
                Weighted { weight: 1, item: 44}),
           [40, 41, 42, 43, 44]);
        t!(vec!(Weighted { weight: 1, item: 50},
                Weighted { weight: 1, item: 51},
                Weighted { weight: 1, item: 52},
                Weighted { weight: 1, item: 53},
                Weighted { weight: 1, item: 54},
                Weighted { weight: 1, item: 55},
                Weighted { weight: 1, item: 56}),
           [50, 51, 52, 53, 54, 55, 56]);
    }

    #[test]
    fn test_weighted_clone_initialization() {
        let initial : Weighted<u32> = Weighted {weight: 1, item: 1};
        let clone = initial.clone();
        assert_eq!(initial.weight, clone.weight);
        assert_eq!(initial.item, clone.item);
    }

    #[test] #[should_panic]
    fn test_weighted_clone_change_weight() {
        let initial : Weighted<u32> = Weighted {weight: 1, item: 1};
        let mut clone = initial.clone();
        clone.weight = 5;
        assert_eq!(initial.weight, clone.weight);
    }

    #[test] #[should_panic]
    fn test_weighted_clone_change_item() {
        let initial : Weighted<u32> = Weighted {weight: 1, item: 1};
        let mut clone = initial.clone();
        clone.item = 5;
        assert_eq!(initial.item, clone.item);

    }

    #[test] #[should_panic]
    fn test_weighted_choice_no_items() {
        WeightedChoice::<isize>::new(vec![]);
    }
    #[test] #[should_panic]
    fn test_weighted_choice_zero_weight() {
        WeightedChoice::new(vec![Weighted { weight: 0, item: 0},
                                  Weighted { weight: 0, item: 1}]);
    }
    #[test] #[should_panic]
    fn test_weighted_choice_weight_overflows() {
        let x = ::std::u32::MAX / 2; // x + x + 2 is the overflow
        WeightedChoice::new(vec![Weighted { weight: x, item: 0 },
                                  Weighted { weight: 1, item: 1 },
                                  Weighted { weight: x, item: 2 },
                                  Weighted { weight: 1, item: 3 }]);
    }
}

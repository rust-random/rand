use crate::RngCore;

pub(crate) struct CoinFlipper<R: RngCore> {
    pub rng: R,
    chunk: u32,
    chunk_remaining: u32,
}

impl<R: RngCore> CoinFlipper<R> {
    pub fn new(rng: R) -> Self {
        Self {
            rng,
            chunk: 0,
            chunk_remaining: 0,
        }
    }

    #[inline]
    /// Returns true with a probability of 1 / d
    /// Uses an expected two bits of randomness
    pub fn gen_ratio_one_over(&mut self, d: usize) -> bool {
        // This uses the same logic as `gen_ratio` but is optimized for the case that the starting numerator is one (which it always is for `Sequence::Choose()`)

        // In this case (unlike in `gen_ratio`), this way of calculating c is always accurate
        let c = (usize::BITS - 1 - d.leading_zeros()).min(32);

        if self.flip_until_tails(c) {
            let numerator = 1 << c;
            return self.gen_ratio(numerator, d);
        } else {
            return false;
        }
    }

    #[inline]
    /// Returns true with a probability of n / d
    /// Uses an expected two bits of randomness
    fn gen_ratio(&mut self, mut n: usize, d: usize) -> bool {
        // Explanation:        
        // We are trying to return true with a probability of n / d
        // If n >= d, we can just return true
        // Otherwise there are two possibilities 2n < d and 2n >= d
        // In either case we flip a coin.
        // If 2n < d
        //  If it comes up tails, return false
        //  If it comes up heads, double n and start again
        //  This is fair because (0.5 * 0) + (0.5 * 2n / d) = n / d and 2n is less than d (if 2n was greater than d we would effectively round it down to 1 by returning true)
        // If 2n >= d
        //   If it comes up tails, set n to 2n - d and start again
        //   If it comes up heads, return true
        //   This is fair because (0.5 * 1) + (0.5 * (2n - d) / d) = n / d
        //   Note that if 2n = d and the coin comes up tails, n will be set to 0 before restarting which is equivalent to returning false.

        // As a performance optimization we can flip multiple coins at once (using the `lzcnt` intrinsic)
        // We can check up to 32 flips at once but we only receive one bit of information - all heads or at least one tail.
        // c is the number of coins to flip.
        // If 2n < d, c is the highest number such that n * 2^c < d and c <= 32.
        // If the result is all heads, then set n to n * 2^c
        // If there was at least one tail, return false
        // If 2n >= d, the order of the heads and tails matters so we flip one coin at a time - c = 1 

        while n < d {
            //Estimate c by counting leading zeros. This will either give the correct c, or c + 1
            let mut c = (n.leading_zeros() - d.leading_zeros()).min(32).max(1);


            // set next_n to n * 2^c (checked_shl will fail if 2n >= `usize::max`)
            if let Some(mut next_n) = n.checked_shl(c) {               

                // Check here that our estimate for c was correct, if not, lower it by one
                if next_n > d && c > 1 {
                    next_n >>= 1;
                    c -= 1;
                }

                if self.flip_until_tails(c) {
                    //All heads
                    //if 2n < d, set n to 2n
                    //if 2n >= d, the while loop will exit and we will return `true`
                    n = next_n
                } else {
                    //At least one tail - either return false or set n to 2n-d
                    n = next_n.saturating_sub(d);
                    
                    if n == 0 {                        
                        //Because we used saturating_sub, n will be zero if 2n was less than d or 2n was equal to d, in either case we can return false.
                        return false;
                    }
                }
            } else {
                // This branch will only be reached when 2n >= `usize::max`
                // Obviously 2n > d
                if self.flip_until_tails(1) {
                    //heads
                    return true;
                } else {
                    //tails
                    n = n.saturating_add(n).saturating_sub(d); // set n to 2n -d
                }
            }
        }
        true
    }
        
    /// If the next `c` bits of randomness are all zeroes, consume them and return true.
    /// Otherwise return false and consume the number of zeroes plus one
    /// Generates new bits of randomness when necessary (int 32 bit chunks)
    /// Has a one in 2 to the `c` chance of returning true
    /// `c` must be less than or equal to 32
    fn flip_until_tails(&mut self, mut c: u32) -> bool {
        debug_assert!(c <= 32); //If `c` > 32 this wil always return false
                                //Note that zeros on the left of the chunk represent heads. It needs to be this way round because zeros are filled in when left shifting
        loop {
            let zeros = self.chunk.leading_zeros();

            if zeros < c {
                // The happy path - we found a 1 and can return false
                // Note that because a 1 bit was detected, we cannot have run out of random bits so we don't need to check

                // First consume all of the bits read
                self.chunk = self.chunk.wrapping_shl(zeros + 1);
                self.chunk_remaining = self.chunk_remaining.saturating_sub(zeros + 1);
                return false;
            } else {
                // The number of zeros is larger than `c`
                //There are two possibilities
                if let Some(new_remaining) = self.chunk_remaining.checked_sub(c) {
                    //Those zeroes were all part of our random chunk, so throw away `c` bits of randomness and return true
                    self.chunk_remaining = new_remaining;
                    self.chunk <<= c;
                    return true;
                } else {
                    // Some of those zeroes were part of the random chunk and some were part of the space behind it
                    c -= self.chunk_remaining; //Take into account the zeroes that were random

                    // Generate a new chunk
                    self.chunk = self.rng.next_u32();
                    self.chunk_remaining = 32; //TODO change back to U32::BITS
                                               //Go back to start of loop
                }
            }
        }
    }
}
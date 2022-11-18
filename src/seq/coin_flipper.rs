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
    /// Returns true with a probability of numerator / denominator
    /// Uses an expected two bits of randomness
    pub fn gen_ratio(&mut self, mut numerator: usize, denominator: usize) -> bool {
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
        //   If it comes up tails, set n to 2n - d
        //   If it comes up heads, return true
        //   This is fair because (0.5 * 1) + (0.5 * (2n - d) / d) = n / d

        while numerator < denominator {
            //The exponent is the number of heads that need to be won in a row to not return false
            let exponent = numerator.leading_zeros() - denominator.leading_zeros();

            if exponent > 1 {
                //n * 2^exponent < d
                if self.flip_until_tails(exponent) {
                    // all heads
                    numerator <<= exponent;
                } else {
                    // a tails somewhere
                    return false;
                }
            }
            //Otherwise n * 2 is either greater than or very close to d
            else if self.flip_until_tails(1) {
                // Heads - double n.
                // If it is now larger than d the loop will exit a
                numerator = numerator.saturating_mul(2);
            } else {
                // Tails
                // If 2n < d return false
                // Else set n to 2n -d

                numerator = numerator.wrapping_sub(denominator).wrapping_add(numerator);
                if numerator > denominator {
                    //This is equivalent to checking if 2n < d (hence the wrapping)
                    return false;
                }
            }
        }
        true
    }

    #[inline]
    /// If the next n bits of randomness are all zeroes, consume them and return true.
    /// Otherwise return false and consume the number of zeroes plus one
    /// Generates new bits of randomness when necessary (int 32 bit chunks)
    /// Has a one in 2 to the n chance of returning true
    fn flip_until_tails(&mut self, mut n: u32) -> bool {
        //Note that zeros on the left of the chunk represent heads. It needs to be this way round because zeros are filled in when left shifting
        loop {
            let zeros = self.chunk.leading_zeros();

            if zeros < n {
                // The happy path - we found a 1 and can return false
                // Note that because a 1 bit was detected, we cannot have run out of random bits so we don't need to check

                // First consume all of the bits read
                self.chunk = self.chunk.wrapping_shl(zeros + 1);
                self.chunk_remaining = self.chunk_remaining.saturating_sub(zeros + 1);
                return false;
            } else {
                // The number of zeros is larger than n
                //There are two possibilities
                if let Some(new_remaining) = self.chunk_remaining.checked_sub(n) {
                    //Those zeroes were all part of our random chunk, so throw away n bits of randomness and return true
                    self.chunk_remaining = new_remaining;
                    self.chunk <<= n;
                    return true;
                } else {
                    // Some of those zeroes were part of the random chunk and some were part of the space behind it
                    n -= self.chunk_remaining; //Take into account the zeroes that were random

                    // Generate a new chunk
                    self.chunk = self.rng.next_u32();
                    self.chunk_remaining = 32; //TODO change back to U32::BITS
                                               //Go back to start of loop
                }
            }
        }
    }
}

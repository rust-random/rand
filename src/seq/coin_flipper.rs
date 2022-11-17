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
    /// Returns true with a probability of 1 / denominator.
    /// Uses an expected two bits of randomness
    pub fn gen_ratio_one_over(&mut self, denominator: usize) -> bool {
        //For this case we can use an optimization, checking a large number of bits at once. If all those bits are successful, then we specialize
        let n = usize::BITS - denominator.leading_zeros() - 1;

        if !self.all_next(n) {
            return false;
        }

        self.gen_ratio(1 << n, denominator)
    }

    #[inline]
    /// Returns true with a probability of numerator / denominator
    /// Uses an expected two bits of randomness
    fn gen_ratio(&mut self, mut numerator: usize, denominator: usize) -> bool {
        // Explanation:
        // We are trying to return true with a probability of n / d
        // If n >= d, we can just return true
        // Otherwise there are two possibilities 2n < d and 2n >= d
        // In either case we flip a coin.
        // If 2n < d
        //  If it comes up tails, return false
        //  If it comes up heads, double n and start again
        //  This is fair because (0.5 * 0) + (0.5 * 2n / d) = n / d and 2n is less than d (if 2n was greater than d we would effectively round it down to 1)
        // If 2n >= d
        //   If it comes up tails, set n to 2n - d
        //   If it comes up heads, return true
        //   This is fair because (0.5 * 1) + (0.5 * (2n - d) / d) = n / d

        while numerator < denominator {
            if let Some(next_numerator) = numerator.checked_mul(2) {
                //This condition will usually be true

                if self.next() {
                    //Heads
                    numerator = next_numerator; //if 2n >= d we this will be checked at the start of the next loop
                } else {
                    //Tails
                    if next_numerator < denominator {
                        return false; //2n < d
                    }
                    numerator = next_numerator - denominator; //2n was greater than d so set it to 2n - d
                }
            } else {
                //Special branch just for massive numbers.
                //2n > usize::max >= d so 2n >= d
                if self.next() {
                    //heads
                    return true;
                }
                //Tails
                numerator = numerator.wrapping_sub(denominator).wrapping_add(numerator);
                //2n - d
            }
        }
        true
    }

    #[inline]
    /// Consume one bit of randomness
    /// Has a one in two chance of returning true
    fn next(&mut self) -> bool {
        if let Some(new_rem) = self.chunk_remaining.checked_sub(1) {
            self.chunk_remaining = new_rem;
        } else {
            self.chunk = self.rng.next_u32();
            self.chunk_remaining = u32::BITS - 1;
        };

        let result = self.chunk.trailing_zeros() > 0; //TODO check if there is a faster test the last bit
        self.chunk = self.chunk.wrapping_shr(1);
        result
    }

    #[inline]
    /// If the next n bits of randomness are all zeroes, consume them and return true.
    /// Otherwise return false and consume the number of zeroes plus one
    /// Has a one in 2 to the n chance of returning true
    fn all_next(&mut self, mut n: u32) -> bool {
        let mut zeros = self.chunk.trailing_zeros();
        while self.chunk_remaining < n {
            //Check we have enough randomness left
            if zeros >= self.chunk_remaining {
                n -= self.chunk_remaining; // Remaining bits are zeroes, we will need to generate more bits and continue
            } else {
                self.chunk_remaining -= zeros + 1; //There was a one in the remaining bits so we can consume it and continue
                self.chunk >>= zeros + 1;
                return false;
            }
            self.chunk = self.rng.next_u32();
            self.chunk_remaining = u32::BITS;
            zeros = self.chunk.trailing_zeros();
        }

        let result = zeros >= n;
        let bits_to_consume = if result { n } else { zeros + 1 };
        self.chunk = self.chunk.wrapping_shr(bits_to_consume);
        self.chunk_remaining = self.chunk_remaining.saturating_sub(bits_to_consume);

        result
    }
}

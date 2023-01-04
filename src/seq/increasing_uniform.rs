use crate::{Rng, RngCore};

/// Similar to a Uniform distribution, but after returning a number in the range [0,n], n is increased by 1.
pub(crate) struct IncreasingUniform<R: RngCore> {
    pub rng: R,
    n: u32,
    //TODO(opt): this should depend on RNG word size
    chunk: u32, //Chunk is a random number in [0, (n + 1) * (n + 2) *..* (n + chunk_remaining) )
    chunk_remaining: u8,
}

impl<R: RngCore> IncreasingUniform<R> {
    /// Create a dice roller.
    /// The next item returned will be a random number in the range [0,n]
    pub fn new(rng: R, n: u32) -> Self {
        let chunk_remaining = if n == 0 { 1 } else { 0 }; // If n = 0, the first number returned will always be 0, so we don't need to generate a random number
        Self {
            rng,
            n,
            chunk: 0,
            chunk_remaining,
        }
    }

    /// Returns a number in [0,n] and increments n by 1.
    /// Generates new random bits as needed
    /// Panics if `n >= u32::MAX`
    #[inline]
    pub fn next_index(&mut self) -> usize {
        let next_n = self.n + 1;

        let next_chunk_remaining = self.chunk_remaining.checked_sub(1).unwrap_or_else(|| {
            //If the chunk is empty, generate a new chunk
            let (bound, remaining) = calculate_bound_u32(next_n);
            //bound = (n + 1) * (n + 2) *..* (n + remaining)
            self.chunk = self.rng.gen_range(0..bound);
            // Chunk is a random number in [0, (n + 1) * (n + 2) *..* (n + remaining) )

            remaining - 1
        });

        let result = if next_chunk_remaining == 0 {
            //If the chunk is empty we asr
            self.chunk as usize
            // `chunk` is a random number in the range [0..n+1)
            // Because `chunk_remaining` is about to be set to zero, we do not need to clear the chunk here
        } else {
            // `chunk` is a random number in a range that is a multiple of n+1 so r will be a random number in [0..n+1)
            let r = self.chunk % next_n;
            self.chunk /= next_n;
            r as usize
        };

        self.chunk_remaining = next_chunk_remaining;
        self.n = next_n;
        result
    }
}

#[inline]
/// Calculates `bound`, `count` such that bound (m)*(m+1)*..*(m + remaining - 1)
fn calculate_bound_u32(m: u32) -> (u32, u8) {
    #[inline]
    const fn inner(m: u32) -> (u32, u8) {
        let mut product = m;
        let mut current = m + 1;

        loop {
            if let Some(p) = u32::checked_mul(product, current) {
                product = p;
                current += 1;
            } else {
                let count = (current - m) as u8; //Maximum value of 13 for when min is 1 or 2
                return (product, count);
            }
        }
    }

    const RESULT2: (u32, u8) = inner(2);
    if m == 2 {
        return RESULT2; //Making this value a constant instead of recalculating it gives a significant (~50%) performance boost for small shuffles
    }

    inner(m)
}

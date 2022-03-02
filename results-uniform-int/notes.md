Notes on results of uniform int benchmarks
===================

Benchmarks
----------------

We benchmark the following:

-   Low reject: sampling from the range `-1..=2`. Using a small range of size 3
    requires use of rejection sampling for unbiased sampling, but has a very low
    chance of requiring resampling with all methods used. A distribution object
    is constructed during initialisation, then sampled repeatedly.
-   High reject: sampling from the range `MIN..=h` where `MIN` is the type's
    smallest representable value and `h` is 116 for `i8`, 32407 for `i16` and 1
    for all other types. These values were picked to ensure that rejection is
    likely due to a range of size 1 greater than half of the backing type,
    excepting `i8` and `i16` types where a `u32` integer (or `u64`) is typically
    used for sampling; these latter values were picked via exhaustive search.
    This approximately represents a worst case for each method.
-   Single random: sampling from the range `0..=h` where `h` is itself randomly
    sampled from the entire range of the backing type (note that this adds some
    overhead). Each sample uses a new range and uses the
    `sample_single_inclusive` sampling method variant.
-   Distr random: sampling 50 times from a distribution with range `MIN..=h`
    where `h=MIN + x*y` where `x` and `y` are samples of unsigned-integers of
    half the width. This is a late addition (after other benchmarks were run),
    giving potentially more representative results for distributions by using
    varying ranges but biasing these ranges towards the smaller sizes.
-   Single random (revised): the single-random method is adapted to draw 50
    samples from each range sampled as with Distr random.

The last two benchmarks, using 50 samples from a biased random range, display
variance of the uniform sampling algorithms used *far* better than any prior
benchmarks, and in retrospect are the only ones really worth using.

Note that the samples with fixed sampling range share code while the random-
range samples do not, though the code works similarly.

The following sampling methods are compared:

-   Old: the previous method used is benchmarked as a baseline; this method uses
    widening multiply with a rejection zone.
-   Lemire (fixed range only): widening multiply with a rejection test; this is
    essentially the same as the Old method.
-   Bitmask: this method avoids the need for a multiply at the cost of increased
    chance of sample rejection.
-   Canon: the method proposed by Stephen Canon for adoption into Swift. This
    uses widening multiply using 64-bit samples for all types except 128-bit
    integers (which use 128-bit samples). Up to one bias-reduction step is used,
    allowing maximum bias of 1-in-2^64 samples.
-   Canon32: the same as Canon but using 32-bit samples for types up to 32-bits.
    For 64-bit and higher types this is identical to Canon.
-   Canon-reduced: for 8-, 16- and 32-bit types this is simply widening multiply
    using 64-bit samples with no bias-reduction (thus the maximum bias is
    1-in-2^n where n=64-size). For 64- and 128-bit integers this uses Canon's
    method with a single bias reduction step, but where the bias-reduction step
    uses a half-sized integer (32- or 64-bit).
-   Canon-Lemire: as Canon but with more precise bias-reduction step trigger
-   Canon-Unbiased: Canon's method using 64-bit samples (except 128-bit types)
    with as many bias-reduction steps as required (zero bias).
-   ONeill (random-range only): uses the method chosen by O'Neill in her blog post:
    <https://www.pcg-random.org/posts/bounded-rands.html>

Since the backing random number generator may influence the benchmark, we use
the following generators:

-   SmallRng: the currently chosen non-cryptographic RNG for size, quality and
    speed, Xoshiro256++, this is a native 64-bit generator
-   Pcg32 (aka Lcg64Xsh32): a small-fast generator using 64-bit arithmetic to
    generate 32-bit results
-   Pcg64 (aka Lcg128Xsl64): a small-fast generator using 128-bit arithmetic to
    generate 64-bit results
-   ChaCha8Rng: a block RNG developed as a cryptographic generator but with
    reduced cycle count

Benchmarks are done on the following system:

-   AMD Ryzen 7 5800X CPU
-   32 GiB 3200 MT/s


Results
----------

Full results may be viewed here: [report/index.html](https://htmlpreview.github.io/?https://github.com/rust-random/rand/blob/canon-uniform-benches/results-uniform-int/report/index.html).

### i8

Low reject: with ChaCha8Rng, Canon, Canon-Lemire and Canon-Unbiased are approx
half speed of best methods. Pcg32 is similar, with Canon-reduced also being slow.
With other RNGs Bitmask comes out a little ahead while Canon-Unbiased is a little slow.

High reject: same, but Bitmask is about the same as other fast methods.

Single random: with all RNGs, Bitmask is the clear loser (approx half speed).
The Old method also does poorly when using ChaCha8Rng but is otherwise similar
to other methods. Pcg32 places the Canon32 and ONeill methods a little ahead,
otherwise they are similar to most other methods.

Distr random: the Bitmask method displays a huge range in performance (best and
worst times, by an order of magnitude in each case). Other methods have much
lower variance in performance. Canon32 is fastest when using Pcg32 and
Canon-reduced is fastest when using ChaCha8Rng but otherwise these algorithms
display similar performance to other fast algorithms. Lemire and Old methods do
very well when using Pcg32 but are otherwise unremarkable.

Single random (revised): Bitmask has very long fat tails compared to everything
else. Canon32 and Canon-reduced tie for first place; Canon-Lemire and
Canon-Unbiased are a little behind the pack.

### i16

For low-reject, high-reject and single random, the conclusions are very similar to i8 results.

Distr random: benchmarks do show the Canon, Canon-Lemire and Canon-Unbiased
methods being clearly slower with ChaCha8Rng and Pcg32 (including Canon-reduced
with the latter RNG).

Single random (revised): this is similar to i8 results but without any clear winners.

### i32

Low reject: again, Canon, Canon-Lemire and Canon-Unbiased methods are
significiantly slower than other methods when using ChaCha8Rng or Pcg32,
with Canon-reduced also being slower on Pcg32. Canon32 does well with ChaCha8Rng
while Bitmask does well in all cases.

High reject: the Bitmask, Lemire and Old methods all score very poorly (more
than twice the time of other methods). Canon-reduced comes out significantly
ahead with ChaCha8Rng but in other cases is in line with other methods. All
remaining methods score similarly (well).

Single random: Bitmask, ONeill, Canon32 and Old in all cases perform poorly
(though not similarly). Canon-reduced comes out a little ahead when using
ChaCha8Rng and SmallRng while Canon-Unbiased does the best with PCG RNGs.

Distr random: again, the Bitmask method has terrible variance; unfortunately
variance of the Canon32, Lemire and Old methods is only a little lower, making
all of these methods poor choices. Of the remainder, Canon-reduced wins by a
large margin (~40%) with ChaCha8Rng and Canon-Unbiased wins by a small margin
(~10%) with Pcg32 but otherwise these methods, Canon and Canon-Lemire all
display similar performance.

Single random (revised): as with distr-random, Bitmask, Canon32, ONeill and Old
methods have high variance. Of the remaining methods, Canon-reduced comes
ahead; Canon comes next.

### i64

Low reject: all methods perform similarly, though Bitmask is a little ahead
with two RNGs and Old is a little behind with ChaCha8Rng.

High reject: the Bitmask, Lemire and Old methods all perform poorly.
The Canon-Unbiased method is roughly 20-30% slower than the faster methods.
Canon, Canon-Lemire and Canon-reduced methods are tied for 1st place.

Single random: the Canon-Lemire method is ahead of other variants by a
significant margin (20-25%). The ONeill and Canon-Unbiased methods are
consistently the worst, by around 30% compared to most methods (70-90% vs
Canon-Lemire).

Distr random: all methods display large variance in performance. Bitmask is
still easily the worst choice, though Canon-Unbiased is only a little faster.
Canon-Lemire appears fastest overall.

Single random (revised): again, all methods display high variance, and Bitmask
is worst. Canon-Lemire is the best due to having a thinner tail than Canon.

### i128

Low reject: Canon-Unbiased is the slowest; Canon and Canon-Lemire are in some
cases also slow. Bitmask wins by a significant margin in three cases but is the
worst when using SmallRng, where Canon32 wins by a large margin.

High reject: Canon-reduced is easily the fastest. Canon-Unbiased, Lemire and
Old methods are the slowest.

Single random: differences between methods are not huge (at most about 40%).
Bitmask is often the fastest; Canon-reduced also does well.

Distr random: in this case it appears that Canon-Unbiased performs the worst,
with Bitmask potentially being a good choice, though with a long fat tail and
the worst performance with SmallRng. Lemire and Old methods are the fastest
methods on average, except possibly compared to Canon-Lemire when using
SmallRng, and with some of the longest tails (though Canon-Unbiased has longer
tails with two RNGs). Probably Canon-Lemire is the smartest pick, though results
hint that better implementations may be possible (e.g. using fewer random bits
initially).

Single random (revised): here, the Old method is easily the worst. Canon-reduced
may be the best, closely followed by Canon and Canon32.


Analysis and conclusions
---------

### Methodology

Using only two fixed sampling ranges for the distribution methods calculated to
have rejection probabilities near the extremes likely does not give a good
representation of average performance. Using random ranges uniformly distributed
from the type's full available range also does not perfectly align with real
world usage where small ranges tend to be more common than large ones
(e.g. sampling indices within arrays is a common usage).

The revised random range sampling method used by the last to benchmarks
clearly improves over this, displaying variance of uniform sampling methods
well.

### Applicability of a uniform approach

Since our code requires separate implementations for each integer size and for
single-sample vs distribution sampling, we could select the best method
individually for each case. There are however two reasons not to do this:

1.  Code readability. Use of multiple, differing implementations prevents use
    of macros and thus enlarges code size and complexity, increasing the
    difficulty of maintenance and risk of bugs.
2.  The RNG used clearly affects the speed of the method used in several cases,
    hinting that results may further differ with other RNGs and with changes to
    code optimization. Thus, algorithms chosen should be robust choices (good in
    all cases).

That said, the methods as implemented already have some changes at different
integer sizes, e.g. using `max(64, size)` bits for sampling, and `Canon-reduced`
being essentially two different methods.

### Acceptable bias

The original Canon offers fast, low-bias samples: at worst, 1 in 2^64 samples
will be biased, though this is improved with smaller integer sizes to 2^96
samples for `i32`, 2^112 for `i16` and 2^120 for `i8`. Canon32 is a cut-down
version of this allowing 2^32 bias for `i32`, 2^48 bias for `i16` and 2^56 bias
for `i8`. Canon-reduced allows identical bias for types `i8`, `i16` and `i32`
but using a single sample instead of multiple.

In reality, it's a little hard to say what might be acceptable. For most
applications, the worst case above here of 1 in 2^32 samples being biased
would be nigh-impossible to spot, while for scientific simulations more
stringent accuracy may be important.

*Possibly* the best approach would be to support two modes:

-   by default, consider bias no greater than 1-in-2^32 acceptable
-   when a specific flag is used, require perfect accuracy

### Worst-case performance

For some applications, worst-case performance is more important than average
case. While our benchmarks do a fairly good job of demonstrating variance in
performance, they are inherently limited: the Bitmask, Lemire, Old and ONeill
methods all have unbounded worst-case time due to their nature, but the
benchmarks do not really show this (though long tails are often apparent).

If this were the main criteria, then a biased single-sample only method similar
to Canon-reduced (for sizes up to `i32`) would be the best pick. If unbiased
sampling were also required, then Canon-Unbiased would be the best pick
(theoretically unbounded time but with vastly reduced chance of each subsequent
step being required); truely unbiased algorithms with bounded worst-case time
are impossible.

### Repeatability

In certain applications it is useful to be able to yield robustly repeatable
results from random number generators. This is always limited: adding or
removing a sample will always affect the random number stream. On the other
hand, due to uncertainty over the number of repetitions used, simply changing
the range of a uniform distribution may affect the random number stream. We can
*reduce* the chance of this happening by using larger samples or prevent it by
using single-step-only biased algorithms. But should we?

-   Considerations of bias come first
-   Performance should be considered first, at least if performance implications
    are significant
-   If the changes would be value-breaking relative to an existing release, no
-   All else equal, yes, if identified

### Variance

All results display either high variance or low variance, apparently with no
in-between. For example, Canon32 results have low variance below 32 bits but
high variance for ≥ 32 bits.

There are very few cases where average performance of a high-variance algorithm
beats that of a low variance algorithm, e.g. `distr_random_i32/Pcg32/Lemire`
vs `distr_random_i32/Pcg32/Canon`. Nevertheless, the average case win is small,
thus (even without considering performance on other RNGs), a low-variance
algorithm is preferred.

Possibly this is due to branch prediction: algorithms which almost always
require only a single step allow the branch predictor to assume no repetitions
are required, while for those often requiring multiple steps the exact number
required is unpredictable.

This *may* also be the main reason that Canon-Unbiased is less competitive with
other methods: occaisionally requiring extra steps reduces branch-prediction
performance.

### i128 integers

Results for this size hint that none of the current methods are optimal. Likely
modifying Canon-reduced to use a half-width sample initially with an extra
threshold test would improve on existing methods; using the improved initial
threshold from Canon-Lemire may also help.

### Methods

-   Bitmask: this appears to be a poor choice everywhere due to variability of
    performance
-   Canon: less competitive < 32-bits, otherwise generally decent performance
    with bias at most 1-in-2^64
-   Canon-Lemire: less competitive < 32-bits, potentially the best for `i64`
-   Canon-Unbiased: generally poor performance with a couple of surprising wins;
    theoretically the best option for unbiased sampling at least with regards to
    worst-case performance. Might be possible to improve initial guard as in
    Canon-Lemire.
-   Canon-reduced (≤ 32 bits): one of the fastest options, depending on RNG.
    For 64-bit generators this is probably the best choice but Canon32 comes out
    ahead when using 32-bit generators.
-   Canon-reduced (> 32 bits): for `i64` this uses 32-bit samples; this approach
    may *possibly* make sense for 32-bit generators but even there isn't really
    competitive. For `i128` this uses 64-bit samples, and is likely the best
    choice (though see notes on [`i128` integers](#i128-integers) above).
-   Canon32: unsurprisingly this has some wins with Pcg32 (32-bit generator) on
    small types, and generally one of the fastest choices for `i8`. Poor choice
    for `i32` due to high performance variance where the 64-bit Canon variants
    have low variance. Theoretically this is a poor choice when using a 64-bit
    native generator since half the random bits are discarded, however this is
    not really apparent in results for `i8` and `i16`.
-   ONeill (single sampling only): performs well for `i8` and `i16` sizes,
    beaten only by Canon32 and Canon-reduced (both biased), thus this is perhaps
    the best choice for unbiased sampling at these sizes. For `i32` and larger
    variance is high; it *may* still be the fastest average-case unbiased
    algorithm for `i64` but (strangely?) not `i32` nor `i128`.
-   Lemire, Old: these methods are mostly identical, both in code and in
    performance. In quite a few cases they have the best average-case
    performance, however wins are small vs Canon variants while tails are
    longer. For this reason they are not preferred.


Final thoughts
-----------------

There are a few performance quirks displayed in these results which may well be
specific to the AMD Zen3 CPU used in these benchmarks. Comparing results with
other those from other CPUs may affect conclusions. Likely the most significant
difference would be when using a 32-bit CPU.

It would be *nice* if we could select an algorithm at compile-time based on
whether we are using a 32-bit or 64-bit or block RNG. Without this, we are
forced to make slightly more conservative choices.

We must make a choice regarding bias:

1.  We could set a threshold and say, e.g., bias up to 1-in-2^48 is considered
    acceptable in this library. This seems mostly reasonable, though results do
    force us to ask exactly which threshold we should use.
2.  We could allow bias by default, but add a `zero_bias` feature flag and
    select different algorithms in this case. This decision may have
    implications on other algorithms too, although *precision* (e.g. of float
    samples) is (at least partially) a separate issue.
3.  We could simply say "no bias allowed", though this lacks justification,
    especially considering other limitations of computing.

Finally, we should choose whether to allow fundamentally different algorithms
at different sizes and for single vs distribution-object sampling. Note that the
ideal choice of algorithms will be affected by the prior choice regarding bias.


Extension
----------

This work does not consider SIMD types. All methods used here could be adapted
to SIMD, but other adjustments may be sensible: for example, when sampling
`u8x8` it would likely make sense to use only 64- or 128-bit samples per step,
thus using 8- or 16-bits per channel at each step.

It would make sense to narrow the number of methods under investigation before
extending the work to SIMD types.

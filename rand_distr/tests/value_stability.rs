// Copyright 2018 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use average::assert_almost_eq;
use core::fmt::Debug;
use rand::Rng;
use rand_distr::*;

fn get_rng(seed: u64) -> impl rand::Rng {
    // For tests, we want a statistically good, fast, reproducible RNG.
    // PCG32 will do fine, and will be easy to embed if we ever need to.
    const INC: u64 = 11634580027462260723;
    rand_pcg::Pcg32::new(seed, INC)
}

/// We only assert approximate equality since some platforms do not perform
/// identically (i686-unknown-linux-gnu and most notably x86_64-pc-windows-gnu).
trait ApproxEq {
    fn assert_almost_eq(&self, rhs: &Self);
}

impl ApproxEq for f32 {
    fn assert_almost_eq(&self, rhs: &Self) {
        assert_almost_eq!(self, rhs, 1e-6);
    }
}
impl ApproxEq for f64 {
    fn assert_almost_eq(&self, rhs: &Self) {
        assert_almost_eq!(self, rhs, 1e-14);
    }
}
impl ApproxEq for u64 {
    fn assert_almost_eq(&self, rhs: &Self) {
        assert_eq!(self, rhs);
    }
}
impl<T: ApproxEq> ApproxEq for [T; 2] {
    fn assert_almost_eq(&self, rhs: &Self) {
        self[0].assert_almost_eq(&rhs[0]);
        self[1].assert_almost_eq(&rhs[1]);
    }
}
impl<T: ApproxEq> ApproxEq for [T; 3] {
    fn assert_almost_eq(&self, rhs: &Self) {
        self[0].assert_almost_eq(&rhs[0]);
        self[1].assert_almost_eq(&rhs[1]);
        self[2].assert_almost_eq(&rhs[2]);
    }
}

fn test_samples<F: Debug + ApproxEq, D: Distribution<F>>(
    seed: u64, distr: D, expected: &[F],
) {
    let mut rng = get_rng(seed);
    for val in expected {
        let x = rng.sample(&distr);
        x.assert_almost_eq(val);
    }
}

#[test]
fn binominal_stability() {
    // We have multiple code paths: np < 10, p > 0.5
    test_samples(353, Binomial::new(2, 0.7).unwrap(), &[1, 1, 2, 1]);
    test_samples(353, Binomial::new(20, 0.3).unwrap(), &[7, 7, 5, 7]);
    test_samples(353, Binomial::new(2000, 0.6).unwrap(), &[1194, 1208, 1192, 1210]);
}

#[test]
fn geometric_stability() {
    test_samples(464, StandardGeometric, &[3, 0, 1, 0, 0, 3, 2, 1, 2, 0]);
    
    test_samples(464, Geometric::new(0.5).unwrap(), &[2, 1, 1, 0, 0, 1, 0, 1]);
    test_samples(464, Geometric::new(0.05).unwrap(), &[24, 51, 81, 67, 27, 11, 7, 6]);
    test_samples(464, Geometric::new(0.95).unwrap(), &[0, 0, 0, 0, 1, 0, 0, 0]);

    // expect non-random behaviour for series of pre-determined trials
    test_samples(464, Geometric::new(0.0).unwrap(), &[u64::max_value(); 100][..]);
    test_samples(464, Geometric::new(1.0).unwrap(), &[0; 100][..]);
}

#[test]
fn hypergeometric_stability() {
    // We have multiple code paths based on the distribution's mode and sample_size
    test_samples(7221, Hypergeometric::new(99, 33, 8).unwrap(), &[4, 3, 2, 2, 3, 2, 3, 1]); // Algorithm HIN
    test_samples(7221, Hypergeometric::new(100, 50, 50).unwrap(), &[23, 27, 26, 27, 22, 24, 31, 22]); // Algorithm H2PE
}

#[test]
fn unit_ball_stability() {
    test_samples(2, UnitBall, &[
        [0.018035709265959987f64, -0.4348771383120438, -0.07982762085055706],
        [0.10588569388223945, -0.4734350111375454, -0.7392104908825501],
        [0.11060237642041049, -0.16065642822852677, -0.8444043930440075]
    ]);
}

#[test]
fn unit_circle_stability() {
    test_samples(2, UnitCircle, &[
        [-0.9965658683520504f64, -0.08280380447614634],
        [-0.9790853270389644, -0.20345004884984505],
        [-0.8449189758898707, 0.5348943112253227],
    ]);
}

#[test]
fn unit_sphere_stability() {
    test_samples(2, UnitSphere, &[
        [0.03247542860231647f64, -0.7830477442152738, 0.6211131755296027],
        [-0.09978440840914075, 0.9706650829833128, -0.21875184231323952],
        [0.2735582468624679, 0.9435374242279655, -0.1868234852870203],
    ]);
}

#[test]
fn unit_disc_stability() {
    test_samples(2, UnitDisc, &[
        [0.018035709265959987f64, -0.4348771383120438],
        [-0.07982762085055706, 0.7765329819820659],
        [0.21450745997299503, 0.7398636984333291],
    ]);
}

#[test]
fn pareto_stability() {
    test_samples(213, Pareto::new(1.0, 1.0).unwrap(), &[
        1.0423688f32, 2.1235929, 4.132709, 1.4679428,
    ]);
    test_samples(213, Pareto::new(2.0, 0.5).unwrap(), &[
        9.019295276219136f64,
        4.3097126018270595,
        6.837815045397157,
        105.8826669383772,
    ]);
}

#[test]
fn poisson_stability() {
    test_samples(223, Poisson::new(7.0).unwrap(), &[5.0f32, 11.0, 6.0, 5.0]);
    test_samples(223, Poisson::new(7.0).unwrap(), &[9.0f64, 5.0, 7.0, 6.0]);
    test_samples(223, Poisson::new(27.0).unwrap(), &[28.0f32, 32.0, 36.0, 36.0]);
}


#[test]
fn triangular_stability() {
    test_samples(860, Triangular::new(2., 10., 3.).unwrap(), &[
        5.74373257511361f64,
        7.890059162791258f64,
        4.7256280652553455f64,
        2.9474808121184077f64,
        3.058301946314053f64,
    ]);
}


#[test]
fn normal_inverse_gaussian_stability() {
    test_samples(213, NormalInverseGaussian::new(2.0, 1.0).unwrap(), &[
        0.6568966f32, 1.3744819, 2.216063, 0.11488572,
    ]);
    test_samples(213, NormalInverseGaussian::new(2.0, 1.0).unwrap(), &[
        0.6838707059642927f64,
        2.4447306460569784,
        0.2361045023235968,
        1.7774534624785319,
    ]);
}

#[test]
fn pert_stability() {
    // mean = 4, var = 12/7
    test_samples(860, Pert::new(2., 10., 3.).unwrap(), &[
        4.908681667460367,
        4.014196196158352,
        2.6489397149197234,
        3.4569780580044727,
        4.242864311947118,
    ]);
}

#[test]
fn inverse_gaussian_stability() {
    test_samples(213, InverseGaussian::new(1.0, 3.0).unwrap(),&[
        0.9339157f32, 1.108113, 0.50864697, 0.39849377,
    ]);
    test_samples(213, InverseGaussian::new(1.0, 3.0).unwrap(), &[
        1.0707604954722476f64,
        0.9628140605340697,
        0.4069687656468226,
        0.660283852985818,
    ]);
}

#[test]
fn gamma_stability() {
    // Gamma has 3 cases: shape == 1, shape < 1, shape > 1
    test_samples(223, Gamma::new(1.0, 5.0).unwrap(), &[
        5.398085f32, 9.162783, 0.2300583, 1.7235851,
    ]);
    test_samples(223, Gamma::new(0.8, 5.0).unwrap(), &[
        0.5051203f32, 0.9048302, 3.095812, 1.8566116,
    ]);
    test_samples(223, Gamma::new(1.1, 5.0).unwrap(), &[
        7.783878094584059f64,
        1.4939528171618057,
        8.638017638857592,
        3.0949337228829004,
    ]);

    // ChiSquared has 2 cases: k == 1, k != 1
    test_samples(223, ChiSquared::new(1.0).unwrap(), &[
        0.4893526200348249f64,
        1.635249736808788,
        0.5013580219361969,
        0.1457735613733489,
    ]);
    test_samples(223, ChiSquared::new(0.1).unwrap(), &[
        0.014824404726978617f64,
        0.021602123937134326,
        0.0000003431429746851693,
        0.00000002291755769542258,
    ]);
    test_samples(223, ChiSquared::new(10.0).unwrap(), &[
        12.693656f32, 6.812016, 11.082001, 12.436167,
    ]);

    // FisherF has same special cases as ChiSquared on each param
    test_samples(223, FisherF::new(1.0, 13.5).unwrap(), &[
        0.32283646f32, 0.048049655, 0.0788893, 1.817178,
    ]);
    test_samples(223, FisherF::new(1.0, 1.0).unwrap(), &[
        0.29925257f32, 3.4392934, 9.567652, 0.020074,
    ]);
    test_samples(223, FisherF::new(0.7, 13.5).unwrap(), &[
        3.3196593155045124f64,
        0.3409169916262829,
        0.03377989856426519,
        0.00004041672861036937,
    ]);

    // StudentT has same special cases as ChiSquared
    test_samples(223, StudentT::new(1.0).unwrap(), &[
        0.54703987f32, -1.8545331, 3.093162, -0.14168274,
    ]);
    test_samples(223, StudentT::new(1.1).unwrap(), &[
        0.7729195887949754f64,
        1.2606210611616204,
        -1.7553606501113175,
        -2.377641221169782,
    ]);

    // Beta has two special cases:
    //
    // 1. min(alpha, beta) <= 1
    // 2. min(alpha, beta) > 1
    test_samples(223, Beta::new(1.0, 0.8).unwrap(), &[
        0.8300703726659456,
        0.8134131062097899,
        0.47912589330631555,
        0.25323238071138526,
    ]);
    test_samples(223, Beta::new(3.0, 1.2).unwrap(), &[
        0.49563509121756827,
        0.9551305482256759,
        0.5151181353461637,
        0.7551732971235077,
    ]);
}

#[test]
fn exponential_stability() {
    test_samples(223, Exp1, &[
        1.079617f32, 1.8325565, 0.04601166, 0.34471703,
    ]);
    test_samples(223, Exp1, &[
        1.0796170642388276f64,
        1.8325565304274,
        0.04601166186842716,
        0.3447170217100157,
    ]);

    test_samples(223, Exp::new(2.0).unwrap(), &[
        0.5398085f32, 0.91627824, 0.02300583, 0.17235851,
    ]);
    test_samples(223, Exp::new(1.0).unwrap(), &[
        1.0796170642388276f64,
        1.8325565304274,
        0.04601166186842716,
        0.3447170217100157,
    ]);
}

#[test]
fn normal_stability() {
    test_samples(213, StandardNormal, &[
        -0.11844189f32, 0.781378, 0.06563994, -1.1932899,
    ]);
    test_samples(213, StandardNormal, &[
        -0.11844188827977231f64,
        0.7813779637772346,
        0.06563993969580051,
        -1.1932899004186373,
    ]);

    test_samples(213, Normal::new(0.0, 1.0).unwrap(), &[
        -0.11844189f32, 0.781378, 0.06563994, -1.1932899,
    ]);
    test_samples(213, Normal::new(2.0, 0.5).unwrap(), &[
        1.940779055860114f64,
        2.3906889818886174,
        2.0328199698479,
        1.4033550497906813,
    ]);

    test_samples(213, LogNormal::new(0.0, 1.0).unwrap(), &[
        0.88830346f32, 2.1844804, 1.0678421, 0.30322206,
    ]);
    test_samples(213, LogNormal::new(2.0, 0.5).unwrap(), &[
        6.964174338639032f64,
        10.921015733601452,
        7.6355881556915906,
        4.068828213584092,
    ]);
}

#[test]
fn weibull_stability() {
    test_samples(213, Weibull::new(1.0, 1.0).unwrap(), &[
        0.041495778f32, 0.7531094, 1.4189332, 0.38386202,
    ]);
    test_samples(213, Weibull::new(2.0, 0.5).unwrap(), &[
        1.1343478702739669f64,
        0.29470010050655226,
        0.7556151370284702,
        7.877212340241561,
    ]);
}

#[cfg(feature = "alloc")]
#[test]
fn dirichlet_stability() {
    let mut rng = get_rng(223);
    assert_eq!(
        rng.sample(Dirichlet::new(&[1.0, 2.0, 3.0]).unwrap()),
        vec![0.12941567177708177, 0.4702121891675036, 0.4003721390554146]
    );
    assert_eq!(rng.sample(Dirichlet::new_with_size(8.0, 5).unwrap()), vec![
        0.17684200044809556,
        0.29915953935953055,
        0.1832858056608014,
        0.1425623503573967,
        0.19815030417417595
    ]);
}

#[test]
fn cauchy_stability() {
    test_samples(353, Cauchy::new(100f64, 10.0).unwrap(), &[
        77.93369152808678f64,
        90.1606912098641,
        125.31516221323625,
        86.10217834773925,
    ]);

    // Unfortunately this test is not fully portable due to reliance on the
    // system's implementation of tanf (see doc on Cauchy struct).
    // We use a lower threshold of 1e-5 here.
    let distr = Cauchy::new(10f32, 7.0).unwrap();
    let mut rng = get_rng(353);
    let expected = [15.023088, -5.446413, 3.7092876, 3.112482];
    for &a in expected.iter() {
        let b = rng.sample(&distr);
        assert_almost_eq!(a, b, 1e-5);
    }
}

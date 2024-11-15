// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

mod ks;
use ks::test_continuous;
use special::Primitive;

#[test]
fn skew_normal() {
    fn cdf(x: f64, location: f64, scale: f64, shape: f64) -> f64 {
        let norm = (x - location) / scale;
        phi(norm) - 2.0 * owen_t(norm, shape)
    }

    let parameters = [(0.0, 1.0, 5.0), (1.0, 10.0, -5.0), (-1.0, 0.00001, 0.0)];

    for (seed, (location, scale, shape)) in parameters.into_iter().enumerate() {
        let dist = rand_distr::SkewNormal::new(location, scale, shape).unwrap();
        test_continuous(seed as u64, dist, |x| cdf(x, location, scale, shape));
    }
}

/// [1] Patefield, M. (2000). Fast and Accurate Calculation of Owen’s T Function.
///     Journal of Statistical Software, 5(5), 1–25.
///     https://doi.org/10.18637/jss.v005.i05
///
/// This function is ported to Rust from the Fortran code provided in the paper
fn owen_t(h: f64, a: f64) -> f64 {
    let absh = h.abs();
    let absa = a.abs();
    let ah = absa * absh;

    let mut t;
    if absa <= 1.0 {
        t = tf(absh, absa, ah);
    } else if absh <= 0.67 {
        t = 0.25 - znorm1(absh) * znorm1(ah) - tf(ah, 1.0 / absa, absh);
    } else {
        let normh = znorm2(absh);
        let normah = znorm2(ah);
        t = 0.5 * (normh + normah) - normh * normah - tf(ah, 1.0 / absa, absh);
    }

    if a < 0.0 {
        t = -t;
    }

    fn tf(h: f64, a: f64, ah: f64) -> f64 {
        let rtwopi = 0.159_154_943_091_895_35;
        let rrtpi = 0.398_942_280_401_432_7;

        let c2 = [
            0.999_999_999_999_999_9,
            -0.999_999_999_999_888,
            0.999_999_999_982_907_5,
            -0.999_999_998_962_825,
            0.999_999_966_604_593_7,
            -0.999_999_339_862_724_7,
            0.999_991_256_111_369_6,
            -0.999_917_776_244_633_8,
            0.999_428_355_558_701_4,
            -0.996_973_117_207_23,
            0.987_514_480_372_753,
            -0.959_158_579_805_728_8,
            0.892_463_055_110_067_1,
            -0.768_934_259_904_64,
            0.588_935_284_684_846_9,
            -0.383_803_451_604_402_55,
            0.203_176_017_010_453,
            -8.281_363_160_700_499e-2,
            2.416_798_473_575_957_8e-2,
            -4.467_656_666_397_183e-3,
            3.914_116_940_237_383_6e-4,
        ];

        let pts = [
            3.508_203_967_645_171_6e-3,
            3.127_904_233_803_075_6e-2,
            8.526_682_628_321_945e-2,
            0.162_450_717_308_122_77,
            0.258_511_960_491_254_36,
            0.368_075_538_406_975_3,
            0.485_010_929_056_047,
            0.602_775_141_526_185_7,
            0.714_778_842_177_532_3,
            0.814_755_109_887_601,
            0.897_110_297_559_489_7,
            0.957_238_080_859_442_6,
            0.991_788_329_746_297,
        ];

        let wts = [
            1.883_143_811_532_350_3e-2,
            1.856_708_624_397_765e-2,
            1.804_209_346_122_338_5e-2,
            1.726_382_960_639_875_2e-2,
            1.624_321_997_598_985_8e-2,
            1.499_459_203_411_670_5e-2,
            1.353_547_446_966_209e-2,
            1.188_635_160_582_016_5e-2,
            1.007_037_724_277_743_2e-2,
            8.113_054_574_229_958e-3,
            6.041_900_952_847_024e-3,
            3.886_221_701_074_205_7e-3,
            1.679_303_108_454_609e-3,
        ];

        let hrange = [
            0.02, 0.06, 0.09, 0.125, 0.26, 0.4, 0.6, 1.6, 1.7, 2.33, 2.4, 3.36, 3.4, 4.8,
        ];
        let arange = [0.025, 0.09, 0.15, 0.36, 0.5, 0.9, 0.99999];

        let select = [
            [1, 1, 2, 13, 13, 13, 13, 13, 13, 13, 13, 16, 16, 16, 9],
            [1, 2, 2, 3, 3, 5, 5, 14, 14, 15, 15, 16, 16, 16, 9],
            [2, 2, 3, 3, 3, 5, 5, 15, 15, 15, 15, 16, 16, 16, 10],
            [2, 2, 3, 5, 5, 5, 5, 7, 7, 16, 16, 16, 16, 16, 10],
            [2, 3, 3, 5, 5, 6, 6, 8, 8, 17, 17, 17, 12, 12, 11],
            [2, 3, 5, 5, 5, 6, 6, 8, 8, 17, 17, 17, 12, 12, 12],
            [2, 3, 4, 4, 6, 6, 8, 8, 17, 17, 17, 17, 17, 12, 12],
            [2, 3, 4, 4, 6, 6, 18, 18, 18, 18, 17, 17, 17, 12, 12],
        ];

        let ihint = hrange.iter().position(|&r| h < r).unwrap_or(14);

        let iaint = arange.iter().position(|&r| a < r).unwrap_or(7);

        let icode = select[iaint][ihint];
        let m = [
            2, 3, 4, 5, 7, 10, 12, 18, 10, 20, 30, 20, 4, 7, 8, 20, 13, 0,
        ][icode - 1];
        let method = [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 4, 4, 4, 5, 6][icode - 1];

        match method {
            1 => {
                let hs = -0.5 * h * h;
                let dhs = hs.exp();
                let as_ = a * a;
                let mut j = 1;
                let mut jj = 1;
                let mut aj = rtwopi * a;
                let mut tf = rtwopi * a.atan();
                let mut dj = dhs - 1.0;
                let mut gj = hs * dhs;
                loop {
                    tf += dj * aj / (jj as f64);
                    if j >= m {
                        return tf;
                    }
                    j += 1;
                    jj += 2;
                    aj *= as_;
                    dj = gj - dj;
                    gj *= hs / (j as f64);
                }
            }
            2 => {
                let maxii = m + m + 1;
                let mut ii = 1;
                let mut tf = 0.0;
                let hs = h * h;
                let as_ = -a * a;
                let mut vi = rrtpi * a * (-0.5 * ah * ah).exp();
                let mut z = znorm1(ah) / h;
                let y = 1.0 / hs;
                loop {
                    tf += z;
                    if ii >= maxii {
                        tf *= rrtpi * (-0.5 * hs).exp();
                        return tf;
                    }
                    z = y * (vi - (ii as f64) * z);
                    vi *= as_;
                    ii += 2;
                }
            }
            3 => {
                let mut i = 1;
                let mut ii = 1;
                let mut tf = 0.0;
                let hs = h * h;
                let as_ = a * a;
                let mut vi = rrtpi * a * (-0.5 * ah * ah).exp();
                let mut zi = znorm1(ah) / h;
                let y = 1.0 / hs;
                loop {
                    tf += zi * c2[i - 1];
                    if i > m {
                        tf *= rrtpi * (-0.5 * hs).exp();
                        return tf;
                    }
                    zi = y * ((ii as f64) * zi - vi);
                    vi *= as_;
                    i += 1;
                    ii += 2;
                }
            }
            4 => {
                let maxii = m + m + 1;
                let mut ii = 1;
                let mut tf = 0.0;
                let hs = h * h;
                let as_ = -a * a;
                let mut ai = rtwopi * a * (-0.5 * hs * (1.0 - as_)).exp();
                let mut yi = 1.0;
                loop {
                    tf += ai * yi;
                    if ii >= maxii {
                        return tf;
                    }
                    ii += 2;
                    yi = (1.0 - hs * yi) / (ii as f64);
                    ai *= as_;
                }
            }
            5 => {
                let mut tf = 0.0;
                let as_ = a * a;
                let hs = -0.5 * h * h;
                for i in 0..m {
                    let r = 1.0 + as_ * pts[i];
                    tf += wts[i] * (hs * r).exp() / r;
                }
                tf *= a;
                tf
            }
            6 => {
                let normh = znorm2(h);
                let mut tf = 0.5 * normh * (1.0 - normh);
                let y = 1.0 - a;
                let r = (y / (1.0 + a)).atan();
                if r != 0.0 {
                    tf -= rtwopi * r * (-0.5 * y * h * h / r).exp();
                }
                tf
            }
            _ => 0.0,
        }
    }

    // P(0 ≤ Z ≤ x)
    fn znorm1(x: f64) -> f64 {
        phi(x) - 0.5
    }

    // P(x ≤ Z < ∞)
    fn znorm2(x: f64) -> f64 {
        1.0 - phi(x)
    }

    t
}

fn normal_cdf(x: f64, mean: f64, std_dev: f64) -> f64 {
    0.5 * ((mean - x) / (std_dev * core::f64::consts::SQRT_2)).erfc()
}

/// standard normal cdf
fn phi(x: f64) -> f64 {
    normal_cdf(x, 0.0, 1.0)
}

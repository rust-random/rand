// MIT License

// Copyright (c) 2016 Michael Ma

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

/// https://docs.rs/statrs/latest/src/statrs/function/gamma.rs.html#260-347
use special::Primitive;

pub fn gamma_lr(a: f64, x: f64) -> f64 {
    if a.is_nan() || x.is_nan() {
        return f64::NAN;
    }

    if a <= 0.0 || a == f64::INFINITY {
        panic!("a must be positive and finite");
    }
    if x <= 0.0 || x == f64::INFINITY {
        panic!("x must be positive and finite");
    }

    const ACC: f64 = 0.0000000000000011102230246251565;

    if a.abs() < ACC {
        return 1.0;
    }

    if x.abs() < ACC {
        return 0.0;
    }

    let eps = 0.000000000000001;
    let big = 4503599627370496.0;
    let big_inv = 2.220_446_049_250_313e-16;

    let ax = a * x.ln() - x - a.lgamma().0;
    if ax < -709.782_712_893_384 {
        if a < x {
            return 1.0;
        }
        return 0.0;
    }
    if x <= 1.0 || x <= a {
        let mut r2 = a;
        let mut c2 = 1.0;
        let mut ans2 = 1.0;
        loop {
            r2 += 1.0;
            c2 *= x / r2;
            ans2 += c2;

            if c2 / ans2 <= eps {
                break;
            }
        }
        return ax.exp() * ans2 / a;
    }

    let mut y = 1.0 - a;
    let mut z = x + y + 1.0;
    let mut c = 0;

    let mut p3 = 1.0;
    let mut q3 = x;
    let mut p2 = x + 1.0;
    let mut q2 = z * x;
    let mut ans = p2 / q2;

    loop {
        y += 1.0;
        z += 2.0;
        c += 1;
        let yc = y * f64::from(c);

        let p = p2 * z - p3 * yc;
        let q = q2 * z - q3 * yc;

        p3 = p2;
        p2 = p;
        q3 = q2;
        q2 = q;

        if p.abs() > big {
            p3 *= big_inv;
            p2 *= big_inv;
            q3 *= big_inv;
            q2 *= big_inv;
        }

        if q != 0.0 {
            let nextans = p / q;
            let error = ((ans - nextans) / nextans).abs();
            ans = nextans;

            if error <= eps {
                break;
            }
        }
    }
    1.0 - ax.exp() * ans
}

/// https://docs.rs/spfunc/latest/src/spfunc/zeta.rs.html#20-43
pub fn zeta_func(s: f64) -> f64 {
    fn update_akn(akn: &mut Vec<f64>, s: f64) {
        let n = akn.len() - 1;

        let n1 = n as f64 + 1.0;

        akn.iter_mut().enumerate().for_each(|(k, a)| {
            let num = n1;
            let den = n + 1 - k;
            *a *= num / den as f64;
        });
        let p1 = -1.0 / n1;
        let p2 = (n1 / (n1 + 1.0)).powf(s);

        akn.push(p1 * p2 * akn[n]);
    }

    if s == 1.0 {
        return f64::INFINITY;
    }

    let mut akn = vec![1.0];
    let mut two_pow = 0.5;
    let head = 1.0 / (1.0 - 2.0.powf(1.0 - s));
    let mut tail_prev = 0.0;
    let mut tail = two_pow * akn[0];

    while (tail - tail_prev).abs() >= f64::EPSILON {
        update_akn(&mut akn, s);
        two_pow /= 2.0;
        tail_prev = tail;
        tail += two_pow * akn.iter().sum::<f64>();
    }

    head * tail
}

// Copyright 2021 Developers of the Rand project.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/// Number of ticks.
const N: usize = 8;
/// Ticks used for the sparkline.
static TICKS: [char; N] = ['▁', '▂', '▃', '▄', '▅', '▆', '▇', '█'];

/// Render a sparkline of `data` into `buffer`.
pub fn render_u64(data: &[u64], buffer: &mut String) {
    match data.len() {
        0 => {
            return;
        },
        1 => {
            if data[0] == 0 {
                buffer.push(TICKS[0]);
            } else {
                buffer.push(TICKS[N - 1]);
            }
            return;
        },
        _ => {},
    }
    let max = data.iter().max().unwrap();
    let min = data.iter().min().unwrap();
    let scale = ((N - 1) as f64) / ((max - min) as f64);
    for i in data {
        let tick = (((i - min) as f64) * scale) as usize;
        buffer.push(TICKS[tick]);
    }
}

/// Calculate the required capacity for the sparkline, given the length of the
/// input data.
pub fn required_capacity(len: usize) -> usize {
    len * TICKS[0].len_utf8()
}

/// Render a sparkline of `data` into a newly allocated string.
pub fn render_u64_as_string(data: &[u64]) -> String {
    let cap = required_capacity(data.len());
    let mut s = String::with_capacity(cap);
    render_u64(data, &mut s);
    debug_assert_eq!(s.capacity(), cap);
    s
}

/// Render a sparkline of `data` into `buffer`.
pub fn render_f64(data: &[f64], buffer: &mut String) {
    match data.len() {
        0 => {
            return;
        },
        1 => {
            if data[0] == 0. {
                buffer.push(TICKS[0]);
            } else {
                buffer.push(TICKS[N - 1]);
            }
            return;
        },
        _ => {},
    }
    for x in data {
        assert!(x.is_finite(), "can only render finite values");
    }
    let max = data.iter().fold(
        core::f64::NEG_INFINITY, |a, &b| a.max(b));
    let min = data.iter().fold(
        core::f64::INFINITY, |a, &b| a.min(b));
    let scale = ((N - 1) as f64) / (max - min);
    for x in data {
        let tick = ((x - min) * scale) as usize;
        buffer.push(TICKS[tick]);
    }
}

/// Render a sparkline of `data` into a newly allocated string.
pub fn render_f64_as_string(data: &[f64]) -> String {
    let cap = required_capacity(data.len());
    let mut s = String::with_capacity(cap);
    render_f64(data, &mut s);
    debug_assert_eq!(s.capacity(), cap);
    s
}

#[cfg(test)]
mod tests {
    #[test]
    fn render_u64() {
        let data = [2, 250, 670, 890, 2, 430, 11, 908, 123, 57];
        let mut s = String::with_capacity(super::required_capacity(data.len()));
        super::render_u64(&data, &mut s);
        println!("{}", s);
        assert_eq!("▁▂▆▇▁▄▁█▁▁", &s);
    }

    #[test]
    fn render_u64_as_string() {
        let data = [2, 250, 670, 890, 2, 430, 11, 908, 123, 57];
        let s = super::render_u64_as_string(&data);
        println!("{}", s);
        assert_eq!("▁▂▆▇▁▄▁█▁▁", &s);
    }

    #[test]
    fn render_f64() {
        let data = [2., 250., 670., 890., 2., 430., 11., 908., 123., 57.];
        let mut s = String::with_capacity(super::required_capacity(data.len()));
        super::render_f64(&data, &mut s);
        println!("{}", s);
        assert_eq!("▁▂▆▇▁▄▁█▁▁", &s);
    }

    #[test]
    fn render_f64_as_string() {
        let data = [2., 250., 670., 890., 2., 430., 11., 908., 123., 57.];
        let s = super::render_f64_as_string(&data);
        println!("{}", s);
        assert_eq!("▁▂▆▇▁▄▁█▁▁", &s);
    }
}

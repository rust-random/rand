use rand::{prelude::IndexedRandom, rng};

#[test]
fn main() {
    let values: Vec<(i32, f64)> =
        vec![(1, 0.080), (2, 0.0078), (3, 0.012)]
            .into_iter()
            .map(|v| (v.0, f64::powf(v.1, 4.0)))
            .collect();

    for v in &values {
        println!("value={} has weight={:.10}", v.0, v.1);
    }
    let weight_sum: f64 = values.iter().map(|(_, w)| w).sum();
    let weights: Vec<f64> = values.iter().map(|(_, w)| w / weight_sum).collect();
    println!("expected: {weights:?}");

    let largest_weight = values[0].1;

    let mut results = [0u32; 9];

    for _ in 0..100_000 {
        let mut iter = values.choose_multiple_weighted(&mut rng(), 2, |a| a.1 / largest_weight).unwrap();
        let a = iter.next().unwrap().0;
        let b = iter.next().unwrap().0;
        assert!(iter.next().is_none());

        let i = (a - 1) * 3 + b - 1;
        results[i as usize] += 1;
    }

    println!("got following results:");
    for i in 0..9 {
        let i0 = i / 3 + 1;
        let i1 = i % 3 + 1;
        println!("({}, {}):\t{}", i0, i1, results[i]);
    }
    assert!(false);
}

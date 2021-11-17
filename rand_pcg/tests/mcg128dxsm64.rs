use rand_core::{RngCore, SeedableRng};
use rand_pcg::Mcg128Dxsm64;

#[test]
fn test_mcg128dxsm64_advancing() {
    for seed in 0..20 {
        let mut rng1 = Mcg128Dxsm64::seed_from_u64(seed);
        let mut rng2 = rng1.clone();
        for _ in 0..20 {
            rng1.next_u64();
        }
        rng2.advance(20);
        assert_eq!(rng1, rng2);
    }
}

#[test]
fn test_mcg128dxsm64_construction() {
    // Test that various construction techniques produce a working RNG.
    let seed = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let mut rng1 = Mcg128Dxsm64::from_seed(seed);
    assert_eq!(rng1.next_u64(), 1736419716824758620);

    let mut rng2 = Mcg128Dxsm64::from_rng(&mut rng1).unwrap();
    assert_eq!(rng2.next_u64(), 5013833792674855812);

    let mut rng3 = Mcg128Dxsm64::seed_from_u64(0);
    assert_eq!(rng3.next_u64(), 11694217129156289387);
}

#[test]
fn test_mcg128dxsm64_true_values() {
    // Numbers copied from official test suite (C version).
    let mut rng = Mcg128Dxsm64::new(42);

    let mut results = [0u64; 6];
    for i in results.iter_mut() {
        *i = rng.next_u64();
    }
    let expected: [u64; 6] = [
        1193744376336385886,
        15856384575281968806,
        16931219497304505213,
        3384898283218318739,
        8029212987130329299,
        12451071819108019858,
    ];
    assert_eq!(results, expected);
}

#[cfg(feature = "serde1")]
#[test]
fn test_mcg128dxsm64_serde() {
    use bincode;
    use std::io::{BufReader, BufWriter};

    let mut rng = Mcg128Dxsm64::seed_from_u64(0);

    let buf: Vec<u8> = Vec::new();
    let mut buf = BufWriter::new(buf);
    bincode::serialize_into(&mut buf, &rng).expect("Could not serialize");

    let buf = buf.into_inner().unwrap();
    let mut read = BufReader::new(&buf[..]);
    let mut deserialized: Mcg128Dxsm64 =
        bincode::deserialize_from(&mut read).expect("Could not deserialize");

    for _ in 0..16 {
        assert_eq!(rng.next_u64(), deserialized.next_u64());
    }
}

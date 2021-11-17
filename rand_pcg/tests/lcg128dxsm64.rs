use rand_core::{RngCore, SeedableRng};
use rand_pcg::Lcg128Dxsm64;

#[test]
fn test_lcg128dxsm64_advancing() {
    for seed in 0..20 {
        let mut rng1 = Lcg128Dxsm64::seed_from_u64(seed);
        let mut rng2 = rng1.clone();
        for _ in 0..20 {
            rng1.next_u64();
        }
        rng2.advance(20);
        assert_eq!(rng1, rng2);
    }
}

#[test]
fn test_lcg128dxsm64_construction() {
    // Test that various construction techniques produce a working RNG.
    #[rustfmt::skip]
    let seed = [1,2,3,4, 5,6,7,8, 9,10,11,12, 13,14,15,16,
            17,18,19,20, 21,22,23,24, 25,26,27,28, 29,30,31,32];
    let mut rng1 = Lcg128Dxsm64::from_seed(seed);
    assert_eq!(rng1.next_u64(), 2938496153450706928);

    let mut rng2 = Lcg128Dxsm64::from_rng(&mut rng1).unwrap();
    assert_eq!(rng2.next_u64(), 13671986342250143118);

    let mut rng3 = Lcg128Dxsm64::seed_from_u64(0);
    assert_eq!(rng3.next_u64(), 12158872473217103133);
}

#[test]
fn test_lcg128dxsm64_true_values() {
    // Numbers determined using `pcg_engines::setseq_dxsm_128_64` from pcg-cpp.
    let mut rng = Lcg128Dxsm64::new(42, 54);

    let mut results = [0u64; 6];
    for i in results.iter_mut() {
        *i = rng.next_u64();
    }
    let expected: [u64; 6] = [
        11174864637253123094,
        12620051823117815757,
        7952300229545126305,
        9255189934450067754,
        10200075529089579563,
        1435750523078544755,
    ];
    assert_eq!(results, expected);
}

#[cfg(feature = "serde1")]
#[test]
fn test_lcg128dxsm64_serde() {
    use bincode;
    use std::io::{BufReader, BufWriter};

    let mut rng = Lcg128Dxsm64::seed_from_u64(0);

    let buf: Vec<u8> = Vec::new();
    let mut buf = BufWriter::new(buf);
    bincode::serialize_into(&mut buf, &rng).expect("Could not serialize");

    let buf = buf.into_inner().unwrap();
    let mut read = BufReader::new(&buf[..]);
    let mut deserialized: Lcg128Dxsm64 =
        bincode::deserialize_from(&mut read).expect("Could not deserialize");

    for _ in 0..16 {
        assert_eq!(rng.next_u64(), deserialized.next_u64());
    }
}

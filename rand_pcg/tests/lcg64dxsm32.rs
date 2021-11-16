use rand_core::{RngCore, SeedableRng};
use rand_pcg::Lcg64Dxsm32;

#[test]
fn test_lcg64dxsm32_advancing() {
    for seed in 0..20 {
        let mut rng1 = Lcg64Dxsm32::seed_from_u64(seed);
        let mut rng2 = rng1.clone();
        for _ in 0..20 {
            rng1.next_u32();
        }
        rng2.advance(20);
        assert_eq!(rng1, rng2);
    }
}

#[test]
fn test_lcg64dxsm32_construction() {
    // Test that various construction techniques produce a working RNG.
    let seed = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let mut rng1 = Lcg64Dxsm32::from_seed(seed);
    assert_eq!(rng1.next_u64(), 15326956640257357418);

    let mut rng2 = Lcg64Dxsm32::from_rng(&mut rng1).unwrap();
    assert_eq!(rng2.next_u64(), 9546535789493423792);

    let mut rng3 = Lcg64Dxsm32::seed_from_u64(0);
    assert_eq!(rng3.next_u64(), 8666077231411827703);
}

#[test]
fn test_lcg64dxsm32_true_values() {
    // Numbers determined using `pcg_engines::setseq_dxsm_64_32` from pcg-cpp.
    let mut rng = Lcg64Dxsm32::new(42, 54);

    let mut results = [0u32; 6];
    for i in results.iter_mut() {
        *i = rng.next_u32();
    }
    let expected: [u32; 6] = [
        2517356991, 3792124711, 1671170184, 682388248, 3329158020, 526178334,
    ];
    assert_eq!(results, expected);
}

#[cfg(feature = "serde1")]
#[test]
fn test_lcg64dxsm32_serde() {
    use bincode;
    use std::io::{BufReader, BufWriter};

    let mut rng = Lcg64Dxsm32::seed_from_u64(0);

    let buf: Vec<u8> = Vec::new();
    let mut buf = BufWriter::new(buf);
    bincode::serialize_into(&mut buf, &rng).expect("Could not serialize");

    let buf = buf.into_inner().unwrap();
    let mut read = BufReader::new(&buf[..]);
    let mut deserialized: Lcg64Dxsm32 =
        bincode::deserialize_from(&mut read).expect("Could not deserialize");

    for _ in 0..16 {
        assert_eq!(rng.next_u64(), deserialized.next_u64());
    }
}

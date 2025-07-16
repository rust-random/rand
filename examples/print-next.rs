use rand::{rngs::OsRng, RngCore, TryRngCore};

fn main() {
    let mut rng = TryRngCore::unwrap_err(OsRng);
    println!("Next u32: {0:>#18X} = {0:>20}", rng.next_u32());
    println!("Next u64: {0:>#18X} = {0:>20}", rng.next_u64());
}

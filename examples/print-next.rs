use rand::Rng;

fn main() {
    let mut rng = rand::rng();
    println!("Next u32: {0:>#18X} = {0:>20}", rng.next_u32());
    println!("Next u64: {0:>#18X} = {0:>20}", rng.next_u64());
}

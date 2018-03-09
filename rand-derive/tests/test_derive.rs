extern crate rand;
#[macro_use]
extern crate rand_derive;

use rand::{Rng, NewRng, IsaacRng};

#[derive(Clone, Debug, RngCore, SeedableRng)]
struct MyRng(IsaacRng);

fn main() {
    let mut rng = MyRng::new().unwrap();
    println!("Random output: {:?}", rng.gen::<[u32; 4]>());
}

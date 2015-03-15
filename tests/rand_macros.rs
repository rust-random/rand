#![allow(dead_code)]
#![feature(plugin, custom_derive)]
#![plugin(rand_macros)]

extern crate rand;

use rand::Rng;

#[derive_Rand]
struct Foo {
    x: u8,
    y: isize
}

#[derive_Rand]
enum Bar {
    X(char),
    Y(f64)
}

#[test]
fn smoke() {
    let mut rng = rand::XorShiftRng::new_unseeded();

    // check nothing horrible happens internally:
    for _ in 0..100 {
        let _: Foo = rng.gen();
        let _: Bar = rng.gen();
    }
}

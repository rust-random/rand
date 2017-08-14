#![allow(dead_code)]

extern crate rand;
#[macro_use]
extern crate rand_derive;

use rand::Rng;

#[derive(Rand)]
struct Struct {
    x: u16,
    y: Option<f64>,
}

#[derive(Rand)]
struct Tuple(i16, Option<f64>);

#[derive(Rand)]
struct Unit;

#[derive(Rand)]
enum EnumUnit {
    X,
}

#[derive(Rand)]
enum Enum1 {
    X(u8, f32),
}

#[derive(Rand)]
enum Enum2 {
    X(bool),
    Y,
}

#[derive(Rand)]
enum Enum3 {
    X { x: u8, y: isize },
    Y([bool; 4]),
    Z,
}

#[test]
fn smoke() {
    let mut rng = rand::XorShiftRng::new_unseeded();

    // check nothing horrible happens internally:
    for _ in 0..100 {
        let _ = rng.gen::<Struct>();
        let _ = rng.gen::<Tuple>();
        let _ = rng.gen::<Unit>();
        let _ = rng.gen::<EnumUnit>();
        let _ = rng.gen::<Enum1>();
        let _ = rng.gen::<Enum2>();
        let _ = rng.gen::<Enum3>();
    }
}

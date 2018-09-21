rand_derive
====

`#[derive(Rand)]` functionality enabling sampling of random instances.

**This crate is deprecated as of rand 0.5** since the `Rand` trait has been
deprecated and since it appears to have very little use.

This crate has been updated to work with Rand 0.5, however note that it now
implements `Distribution<Self> for Standard` instead of `Rand`.

## Usage
Add this to your `Cargo.toml`:

```toml
[dependencies]
rand = "0.5"
rand_derive = "0.5"
```

and this to your crate root:

```rust
extern crate rand;
#[macro_use]
extern crate rand_derive;
```

## Examples

`#[derive(Rand)]` can be used on any `struct` or `enum` where all fields/variants implement `rand::Rand`.

```rust
#[derive(Debug, Rand)]
struct Foo {
    x: u16,
    y: Option<f64>,
}

#[derive(Debug, Rand)]
enum Bar {
     X{x: u8, y: isize},
     Y([bool; 4]),
     Z,
}
```
Now you can call the `Rng::gen()` function on your custom types.

```rust
use rand::Rng;

let mut rng = rand::thread_rng();

println!("{:?}", rng.gen::<Foo>());
println!("{:?}", rng.gen::<Bar>());
```

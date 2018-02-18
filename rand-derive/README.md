rand_derive
====

`#[derive(Rand)]` functionality for the `rand::Rand` trait.

**This module is deprecated as of rand 0.5**, due in part to breaking changes
in rand and in part to lack of use. Code is preserved because in theory it
should be straightforward to modify for use with rand's new distribution code.

## Usage
Add this to your `Cargo.toml`:

```toml
[dependencies]
rand = "0.4"
rand_macros = "0.2"
```

and this to your crate root:

```rust
extern crate rand;
#[macro_use]
extern crate rand_macros;
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

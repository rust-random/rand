// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A small utility to concatenate the output of an RNG to stdout.

extern crate rand;

use rand::{Rng, NewSeeded, OsRng};
use rand::prng::{XorShiftRng, IsaacRng, Isaac64Rng, ChaChaRng};
use std::collections::HashMap;
use std::env;
use std::io::{self, Write, Error};
use std::iter::Iterator;

fn print_usage(cmd: &String, names: Vec<String>) {
    println!("Usage: {} RNG
where RNG is one of: {:?}

This is a small tool to endlessly contatenate output from an RNG. It can for
example be used with PractRand: ./cat_rng chacha | ./RNG_test stdin",
        cmd, names);
}

type BR = Box<Rng>;

fn main() {
    let mut ctors: HashMap<&'static str,
            Box<Fn() -> Result<BR, ::rand::Error>>> = HashMap::new();
    ctors.insert("os", Box::new(|| OsRng::new().map(|rng| Box::new(rng) as BR)));
    
    ctors.insert("xorshift", Box::new(|| XorShiftRng::new().map(|rng| Box::new(rng) as BR)));
    ctors.insert("isaac", Box::new(|| IsaacRng::new().map(|rng| Box::new(rng) as BR)));
    ctors.insert("isaac64", Box::new(|| Isaac64Rng::new().map(|rng| Box::new(rng) as BR)));
    ctors.insert("chacha", Box::new(|| ChaChaRng::new().map(|rng| Box::new(rng) as BR)));
    
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        print_usage(&args[0], ctors.keys().map(|s| String::from(*s)).collect());
    } else {
        if let Some(ctor) = ctors.get(&*args[1]) {
            let rng = ctor().unwrap();
            cat_rng(rng).unwrap();
        } else {
            println!("Error: unknown RNG: {}", args[1]);
            println!();
            print_usage(&args[0], ctors.keys().map(|s| String::from(*s)).collect());
        }
    }
}

fn cat_rng(mut rng: Box<Rng>) -> Result<(), Error> {
    let mut buf =  [0u8; 32];
    let stdout = io::stdout();
    let mut lock = stdout.lock();
    
    loop {
        rng.fill_bytes(&mut buf);
        lock.write(&buf)?;
    }
}

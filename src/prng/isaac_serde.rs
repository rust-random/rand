// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// https://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! ISAAC serde helper functions.

pub(super) mod rand_size_serde {
    const RAND_SIZE_LEN: usize = 8;
    const RAND_SIZE: usize = 1 << RAND_SIZE_LEN;

    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use serde::de::{Visitor,SeqAccess};
    use serde::de;

    use std::fmt;

    pub fn serialize<T, S>(arr: &[T;RAND_SIZE], ser: S) -> Result<S::Ok, S::Error> 
    where
        T: Serialize,
        S: Serializer 
    {
        use serde::ser::SerializeTuple;

        let mut seq = ser.serialize_tuple(RAND_SIZE)?;

        for e in arr.iter() {
            seq.serialize_element(&e)?;
        }

        seq.end()
    }

    #[inline]
    pub fn deserialize<'de, T, D>(de: D) -> Result<[T;RAND_SIZE], D::Error>
    where
        T: Deserialize<'de>+Default+Copy,
        D: Deserializer<'de>,
    {
        use std::marker::PhantomData;
        struct ArrayVisitor<T> {
            _pd: PhantomData<T>,
        };
        impl<'de,T> Visitor<'de> for ArrayVisitor<T>
        where
            T: Deserialize<'de>+Default+Copy
        {
            type Value = [T; RAND_SIZE];

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("Isaac state array")
            }

            #[inline]
            fn visit_seq<A>(self, mut seq: A) -> Result<[T; RAND_SIZE], A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut out = [Default::default();RAND_SIZE];

                for i in 0..RAND_SIZE {
                    match seq.next_element()? {
                        Some(val) => out[i] = val,
                        None => return Err(de::Error::invalid_length(i, &self)),
                    };
                }

                Ok(out)
            }
        }

        de.deserialize_tuple(RAND_SIZE, ArrayVisitor{_pd: PhantomData})
    }
}

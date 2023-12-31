# Big Int

Simple library for arbitrary-precision, arbitrary-base arithmetic, supporting arbitrarily large integers of any base from 2 to `usize::MAX`.

```rs
use big_int::prelude::*;

let mut a: Loose<10> = "9000000000000000000000000000000000000000".parse().unwrap();
a /= 13.into();
assert_eq!(a, "692307692307692307692307692307692307692".parse().unwrap());

let mut b: Loose<16> = a.convert();
assert_eq!(b, "208D59C8D8669EDC306F76344EC4EC4EC".parse().unwrap());
b >>= 16.into();

let c: Loose<2> = b.convert();
assert_eq!(c, "100000100011010101100111001000110110000110011010011110110111000011".parse().unwrap());

let mut d: Tight<256> = c.convert();
d += vec![15, 90, 0].into();
assert_eq!(d, vec![2, 8, 213, 156, 141, 134, 121, 71, 195].into());

let e: Tight<10> = d.convert();
assert_eq!(format!("{e}"), "37530075201422313411".to_string());
```

This crate contains two primary big int implementations:
* `Loose<BASE>` - A collection of loosely packed ints representing each digit. 
    Very memory inefficient, but with minimal performance overhead.
* `Tight<BASE>` - A collection of tightly packed bits representing each digit.
    Maximally memory efficient; however, the additional indirection adds some performance overhead.

Ints support most basic arithmetic operations, including addition, subtraction, multiplication, 
division, and left/right shifting. Notably, shifting acts on the `BASE` of the associated number, increasing
or decreasing the magnitude by powers of `BASE` as opposed to powers of 2.

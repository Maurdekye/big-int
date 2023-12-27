//! ## `tight` - More compact BigInt, for better memory efficiency

#[allow(unused)]
pub struct TightInt<const BASE: usize> {
    sign: bool,
    data: Vec<u8>,
    digits: usize,
}
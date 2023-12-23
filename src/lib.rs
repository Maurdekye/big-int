use std::{
    cmp::Ordering,
    collections::VecDeque,
    fmt::Display,
    ops::{Add, Deref, DerefMut, Sub, Neg, Mul, AddAssign, SubAssign},
};
use thiserror::Error;

#[derive(Clone, Copy)]
pub struct Alphabet<'a>(&'a [u8]);

impl<'a> Deref for Alphabet<'a> {
    type Target = [u8];

    fn deref(&self) -> &'a Self::Target {
        self.0
    }
}

pub const STANDARD_ALPHABET: Alphabet =
    Alphabet(b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/");
pub const BASE64_ALPHABET: Alphabet =
    Alphabet(b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/");

#[derive(Error, Debug)]
pub enum BigIntError {
    #[error("Base too large: number has {0} digits, alphabet can only represent {1} digits")]
    BaseTooHigh(usize, usize),
}

pub trait GetBack {
    type Item;

    fn get_back(&self, index: usize) -> Option<&Self::Item>;
}

impl<T> GetBack for Vec<T> {
    type Item = T;
    fn get_back(&self, index: usize) -> Option<&Self::Item> {
        self.len()
            .checked_sub(index)
            .and_then(|index| self.get(index))
    }
}

pub trait GetBackMut {
    type Item;

    fn get_back_mut(&mut self, index: usize) -> Option<&mut Self::Item>;
}

impl<T> GetBackMut for Vec<T> {
    type Item = T;
    fn get_back_mut(&mut self, index: usize) -> Option<&mut Self::Item> {
        self.len()
            .checked_sub(index)
            .and_then(|index| self.get_mut(index))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigInt<const BASE: usize>(pub bool, pub Vec<u8>);

impl<const BASE: usize> BigInt<BASE> {
    pub fn display(&self, alphabet: Alphabet) -> Result<String, BigIntError> {
        let digits = self.1
            .iter()
            .map(|digit| {
                alphabet
                    .get(*digit as usize)
                    .and_then(|c| char::from_u32(*c as u32))
                    .ok_or(BigIntError::BaseTooHigh(BASE, alphabet.len()))
            })
            .collect::<Result<String, _>>()?;
        if self.0 {
            Ok(format!("-{digits}"))
        } else {
            Ok(digits)
        }
    }

    pub fn normalized(mut self) -> Self {
        if let Some(pos) = self.1.iter().position(|digit| *digit != 0) {
            if pos > 0 {
                self.1 = self.1[pos..].to_vec();
            }
        }
        if self.1.is_empty() {
            self.0 = false;
        }
        self
    }
}

// impl<const BASE: usize> Deref for BigInt<BASE> {
//     type Target = Vec<u8>;

//     fn deref(&self) -> &Self::Target {
//         &self.1
//     }
// }

// impl<const BASE: usize> DerefMut for BigInt<BASE> {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.1
//     }
// }

impl<const BASE: usize> From<VecDeque<u8>> for BigInt<BASE> {
    fn from(value: VecDeque<u8>) -> Self {
        BigInt(false, value.into()).normalized()
    }
}

impl<const BASE: usize> From<u128> for BigInt<BASE> {
    fn from(mut value: u128) -> Self {
        let base = BASE as u128;
        let mut result = VecDeque::new();
        while value >= base {
            let (new_value, rem) = (value / base, value % base);
            value = new_value;
            result.push_front(rem as u8);
        }
        result.push_front(value as u8);
        result.into()
    }
}

impl<const BASE: usize> From<i128> for BigInt<BASE> {
    fn from(value: i128) -> Self {
        if value < 0 {
            let mut bigint = BigInt::<BASE>::from((-value) as u128);
            bigint.0 = true;
            bigint
        } else {
            BigInt::<BASE>::from(value as u128)
        }
    }
}

macro_rules! bigint_from_int {
    ($b:ident; $($i:ident),*) => {
        $(
            impl<const BASE: usize> From<$i> for BigInt<BASE> {
                fn from(value: $i) -> Self {
                    (value as $b).into()
                }
            }
        )*
    };
}

bigint_from_int!(i128; i8, i16, i32, i64, isize);
bigint_from_int!(u128; u8, u16, u32, u64, usize);

impl<const BASE: usize> Display for BigInt<BASE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.display(STANDARD_ALPHABET)
                .map_err(|_| std::fmt::Error)?
        )
    }
}

impl<const BASE: usize> Neg for BigInt<BASE> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        BigInt(!self.0, self.1)
    }
}

impl<const BASE: usize> Add for BigInt<BASE> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.0 != rhs.0 {
            self - (-rhs)
        } else {
            let mut carry = 0;
            let mut result = VecDeque::with_capacity(self.1.len().max(rhs.1.len()) + 1);
            for i in 1.. {
                match (self.1.get_back(i), rhs.1.get_back(i), carry) {
                    (None, None, 0) => break,
                    (left_digit, right_digit, carry_in) => {
                        let left_digit = left_digit.copied().unwrap_or_default() as u16;
                        let right_digit = right_digit.copied().unwrap_or_default() as u16;
                        let mut sum = left_digit + right_digit + carry_in;
                        if sum >= BASE as u16 {
                            sum -= BASE as u16;
                            carry = 1;
                        } else {
                            carry = 0;
                        }
                        result.push_front(sum as u8);
                    }
                }
            }
            result.into()
        }
    }
}

/// todo: specialized implementation
impl<const BASE: usize> AddAssign for BigInt<BASE> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<const BASE: usize> Sub for BigInt<BASE> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        if self.0 != rhs.0 {
            self + (-rhs)
        } else if rhs > self {
            -(rhs - self)
        } else {
            let self_len = self.1.len();
            let mut result = VecDeque::with_capacity(self_len.max(rhs.1.len()) + 1);
            for i in 1.. {
                match (self.1.get_back(i), rhs.1.get_back(i)) {
                    (None, None) => break,
                    (left_digit, right_digit) => {
                        let mut left_digit = left_digit.copied().unwrap_or_default() as u16;
                        let right_digit = right_digit.copied().unwrap_or_default() as u16;
                        if left_digit < right_digit {
                            for j in i + 1.. {
                                match self.1.get_back_mut(j) {
                                    None => unreachable!("subtraction with overflow"),
                                    Some(digit @ 0) => *digit = BASE as u8 - 1,
                                    Some(digit) => {
                                        *digit -= 1;
                                        break;
                                    }
                                }
                            }
                            left_digit += BASE as u16;
                        }
                        let difference = left_digit - right_digit;
                        result.push_front(difference as u8);
                    }
                }
            }
            result.into()
        }
    }
}

/// todo: specialized implementation
impl<const BASE: usize> SubAssign for BigInt<BASE> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<const BASE: usize> Mul for BigInt<BASE> {
    type Output = Self;

    fn mul(mut self, mut rhs: Self) -> Self::Output {
        let sign = self.0 != rhs.0;
        self.0 = false;
        rhs.0 = false;
        let mut result = BigInt::from(0);
        for i in 1.. {
            if let Some(&digit) = self.1.get_back(i) {
                for _ in 0..digit {
                    result += rhs.clone();
                }
                rhs.1.push(0);
            } else {
                break;
            }
        }
        result.0 = sign;
        result.normalized()
    }
}

impl<const BASE: usize> Ord for BigInt<BASE> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0, other.0) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            _ => cmp(&self.1, &other.1),
        }
    }
}

impl<const BASE: usize> PartialOrd for BigInt<BASE> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn cmp(a: &[u8], b: &[u8]) -> Ordering {
    if a.len() > b.len() {
        Ordering::Greater
    } else if a.len() < b.len() {
        Ordering::Less
    } else {
        match (a.split_first(), b.split_first()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some((a_digit, rest_a)), Some((b_digit, rest_b))) => match a_digit.cmp(b_digit) {
                Ordering::Equal => cmp(rest_a, rest_b),
                ordering => ordering,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_primitive() {
        assert_eq!(BigInt::<10>::from(524_u128), BigInt(false, vec![5, 2, 4]));
        assert_eq!(BigInt::<10>::from(-301_isize), BigInt(true, vec![3, 0, 1]));
        assert_eq!(BigInt::<10>::from(255_u8), BigInt(false, vec![2, 5, 5]));
    }

    #[test]
    fn addition() {
        let a = BigInt::<10>(false, vec![1, 0, 0]);
        let b = BigInt(false, vec![2, 1]);
        assert_eq!(a + b, BigInt(false, vec![1, 2, 1]))
    }

    #[test]
    fn addition_with_carry() {
        let a = BigInt::<10>(false, vec![1, 5]);
        let b = BigInt(false, vec![6]);
        assert_eq!(a + b, BigInt(false, vec![2, 1]))
    }

    #[test]
    fn addition_with_many_carries() {
        let a = BigInt::<10>(false, vec![9, 9, 9, 9, 9]);
        let b = BigInt(false, vec![1]);
        assert_eq!(a + b, BigInt(false, vec![1, 0, 0, 0, 0, 0]))
    }

    #[test]
    fn addition_base_16() {
        let a = BigInt::<16>(false, vec![8]);
        let b = BigInt(false, vec![10]);
        assert_eq!(a + b, BigInt(false, vec![1, 2]))
    }

    #[test]
    fn subtraction() {
        let a = BigInt::<10>::from(55);
        let b = BigInt::from(14);
        assert_eq!(a - b, BigInt::from(41));
    }

    #[test]
    fn subtraction_with_borrow() {
        let a = BigInt::<10>::from(12);
        let b = BigInt::from(4);
        assert_eq!(a - b, BigInt::from(8));
    }

    #[test]
    fn subtraction_with_many_borrows() {
        let a = BigInt::<10>::from(100000);
        let b = BigInt::from(1);
        assert_eq!(a - b, BigInt::from(99999));
    }

    #[test]
    fn subtraction_with_overflow() {
        let a = BigInt::<10>::from(50);
        let b = BigInt::from(75);
        assert_eq!(a - b, BigInt::from(-25));
    }

    #[test]
    fn multiplication() {
        let a = BigInt::<10>::from(13);
        let b = BigInt::from(5);
        assert_eq!(a * b, BigInt::from(65));
    }
}

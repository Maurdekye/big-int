use std::{
    cmp::Ordering,
    collections::VecDeque,
    fmt::Display,
    ops::{Add, AddAssign, Deref, Div, Mul, Neg, Sub, SubAssign},
    str::FromStr,
};
use thiserror::Error;

#[derive(Clone, Copy)]
pub struct Alphabet<'a>(&'a str);

impl<'a> Deref for Alphabet<'a> {
    type Target = str;

    fn deref(&self) -> &'a Self::Target {
        self.0
    }
}

pub const STANDARD_ALPHABET: Alphabet =
    Alphabet("0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/");
pub const BASE64_ALPHABET: Alphabet =
    Alphabet("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/");

#[derive(Error, Debug, PartialEq, Eq)]
pub enum BigIntError {
    #[error("base too large: number has {0} digits, alphabet can only represent {1} digits")]
    BaseTooHigh(usize, usize),
    #[error("parsing failed: {0}")]
    ParseFailed(ParseError),
    #[error("division by zero")]
    DivisionByZero,
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseError {
    #[error("unrecognized character: {0:?}")]
    UnrecognizedCharacter(char),
    #[error("not enough characters")]
    NotEnoughCharacters,
    #[error("char {0:?} is {1}; too large to be represented in base {2}")]
    DigitTooLarge(char, usize, usize),
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

type Digit = u16;
type DoubleDigit = u32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigInt<const BASE: usize>(pub bool, pub Vec<Digit>);

impl<const BASE: usize> BigInt<BASE> {
    pub fn new(digits: Vec<Digit>) -> Self {
        BigInt(false, digits)
    }

    pub fn zero() -> Self {
        BigInt(false, vec![0])
    }

    pub fn display(&self, alphabet: Alphabet) -> Result<String, BigIntError> {
        let digits = self
            .1
            .iter()
            .map(|digit| {
                alphabet
                    .chars()
                    .nth(*digit as usize)
                    .ok_or(BigIntError::BaseTooHigh(BASE, alphabet.len()))
            })
            .collect::<Result<String, _>>()?;
        if self.0 {
            Ok(format!("-{digits}"))
        } else {
            Ok(digits)
        }
    }

    pub fn normalized(self) -> Self {
        match self.1.iter().position(|digit| *digit != 0) {
            None => BigInt(false, vec![0]),
            Some(pos @ 1..) => BigInt(self.0, self.1[pos..].to_vec()),
            _ => self,
        }
    }

    pub fn parse(value: &str, alphabet: Alphabet) -> Result<Self, ParseError> {
        let mut digits = VecDeque::new();
        let (sign, chars) = match value.chars().next() {
            Some('-') => (true, value.chars().skip(1)),
            Some(_) => (false, value.chars().skip(0)),
            None => return Err(ParseError::NotEnoughCharacters),
        };
        for char in chars {
            match alphabet.chars().position(|c| c == char) {
                Some(pos) => {
                    if pos >= BASE {
                        return Err(ParseError::DigitTooLarge(char, pos, BASE));
                    } else {
                        digits.push_back(pos as Digit);
                    }
                }
                None => return Err(ParseError::UnrecognizedCharacter(char)),
            }
        }
        if digits.is_empty() {
            Err(ParseError::NotEnoughCharacters)
        } else {
            Ok(BigInt(sign, digits.into()).normalized())
        }
    }

    pub fn div_rem(mut self, mut other: Self) -> Result<(Self, Self), BigIntError> {
        if other.clone().normalized() == BigInt::zero() {
            return Err(BigIntError::DivisionByZero);
        }
        if other.1.len() > self.1.len() {
            return Ok((BigInt(false, vec![0]), self));
        }
        let sign = self.0 != other.0;
        self.0 = false;
        other.0 = false;
        let quot_digits = self.1.len() - other.1.len() + 1;
        let mut quot = BigInt::new(vec![0; quot_digits]);
        let mut addend = BigInt::new([other.1, vec![0; quot_digits - 1]].concat());
        let mut prod = BigInt::new(vec![0]);

        for digit in 0..quot.1.len() {
            for digit_value in 0..BASE {
                let new_prod = prod.clone() + addend.clone();
                if new_prod > self {
                    quot.1[digit] = digit_value as Digit;
                    break;
                } else {
                    prod = new_prod;
                }
            }
            addend.1.pop();
        }

        quot.0 = sign;
        let mut rem = self - prod;
        if rem != BigInt::zero() {
            rem.0 = sign;
        }

        Ok((quot.normalized(), rem))
    }

    pub fn div_rem_2(mut self, mut other: Self) -> Result<(Self, Self), BigIntError> {
        if other.clone().normalized() == BigInt::zero() {
            return Err(BigIntError::DivisionByZero);
        }
        if other.1.len() > self.1.len() {
            return Ok((BigInt(false, vec![0]), self));
        }
        let sign = self.0 != other.0;
        self.0 = false;
        other.0 = false;
        let quot_digits = self.1.len() - other.1.len() + 1;
        let mut quot = BigInt::new(vec![0; quot_digits]);
        let mut prod = BigInt::new(vec![0]);
        let mut addend: BigInt<BASE> = BigInt::new([other.1, vec![0; quot_digits - 1]].concat());
        let mut addends = Vec::new();
        let mut power = 1;
        while power < BASE {
            addends.push(addend.clone());
            addend += addend.clone();
            power <<= 1;
        }

        for digit in 0..quot.1.len() {
            let mut digit_value = 0;
            for power in (0..addends.len()).rev() {
                let new_digit_value = digit_value + (1 << power);
                let new_prod = prod.clone() + addends[power].clone();
                if new_prod < self {
                    digit_value = new_digit_value;
                    prod = new_prod;
                }
                addends[power].1.pop();
            }
            quot.1[digit] = digit_value;
        }

        quot.0 = sign;
        let mut rem = self - prod;
        if rem != BigInt::zero() {
            rem.0 = sign;
        }

        Ok((quot.normalized(), rem))
    }

    pub fn convert<const TO: usize>(mut self) -> BigInt<TO> {
        let mut digits = VecDeque::new();
        let to_base = BigInt::<BASE>::from(TO);
        while self > to_base {
            let (quot, rem) = self.div_rem(to_base.clone()).unwrap();
            self = quot;
            digits.push_front(Digit::from(rem));
        }
        BigInt::<TO>(self.0, digits.into()).normalized()
    }
}

impl<const BASE: usize> Default for BigInt<BASE> {
    fn default() -> Self {
        BigInt(false, vec![0])
    }
}

impl<const BASE: usize> FromStr for BigInt<BASE> {
    type Err = BigIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s, STANDARD_ALPHABET).map_err(BigIntError::ParseFailed)
    }
}

impl<const BASE: usize> From<VecDeque<Digit>> for BigInt<BASE> {
    fn from(value: VecDeque<Digit>) -> Self {
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
            result.push_front(rem as Digit);
        }
        result.push_front(value as Digit);
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

macro_rules! int_from_bigint {
    ($(($i:ident, $u:ident)),*) => {
        $(
            impl<const BASE: usize> From<BigInt<BASE>> for $i {
                fn from(value: BigInt<BASE>) -> Self {
                    let mut digits = value.1;
                    let mut total: $i = 0;
                    let mut place: $i = 1;
                    while let Some(digit) = digits.pop() {
                        total += (digit as $i) * place;
                        place *= BASE as $i;
                    }
                    if value.0 {
                        total = -total;
                    }
                    total
                }
            }

            impl<const BASE: usize> From<BigInt<BASE>> for $u {
                fn from(value: BigInt<BASE>) -> Self {
                    $i::from(value) as $u
                }
            }
        )*
    };
}

int_from_bigint!((i128, u128), (i64, u64), (i32, u32), (i16, u16), (i8, u8));

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
                        let left_digit = left_digit.copied().unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.copied().unwrap_or_default() as DoubleDigit;
                        let mut sum = left_digit + right_digit + carry_in;
                        if sum >= BASE as DoubleDigit {
                            sum -= BASE as DoubleDigit;
                            carry = 1;
                        } else {
                            carry = 0;
                        }
                        result.push_front(sum as Digit);
                    }
                }
            }
            let mut result: BigInt<BASE> = result.into();
            result.0 = self.0;
            result
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
                        let mut left_digit = left_digit.copied().unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.copied().unwrap_or_default() as DoubleDigit;
                        if left_digit < right_digit {
                            for j in i + 1.. {
                                match self.1.get_back_mut(j) {
                                    None => unreachable!("subtraction with overflow"),
                                    Some(digit @ 0) => *digit = (BASE - 1) as Digit,
                                    Some(digit) => {
                                        *digit -= 1;
                                        break;
                                    }
                                }
                            }
                            left_digit += BASE as DoubleDigit;
                        }
                        let difference = left_digit - right_digit;
                        result.push_front(difference as Digit);
                    }
                }
            }
            let mut result: BigInt<BASE> = result.into();
            result.0 = self.0;
            result
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

impl<const BASE: usize> Div for BigInt<BASE> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).unwrap().0
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

fn cmp(a: &[Digit], b: &[Digit]) -> Ordering {
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
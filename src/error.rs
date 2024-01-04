//! big int errors.

use thiserror::Error;

/// Represents an error with regards to a big int operation.
#[derive(Error, Debug, PartialEq, Eq)]
pub enum BigIntError {
    #[error("base too large: number has {0} digits, alphabet can only represent {1} digits")]
    BaseTooHigh(usize, usize),
    #[error("parsing failed: {0}")]
    ParseFailed(ParseError),
    #[error("division by zero")]
    DivisionByZero,
    #[error("exponentiation with negative exponent")]
    NegativeExponentiation,
    #[error("logarithm of non positive number")]
    NonPositiveLogarithm,
    #[error("logarithm with base < 2")]
    LogOfSmallBase,
    #[error("nth root of negative number")]
    NegativeRoot,
    #[error("nth root with root < 2")]
    SmallRoot,
}

/// Represents an error with regards to a big int parsing operation.
#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseError {
    #[error("unrecognized character: {0:?}")]
    UnrecognizedCharacter(char),
    #[error("not enough characters")]
    NotEnoughCharacters,
    #[error("char {0:?} is {1}; too large to be represented in base {2}")]
    DigitTooLarge(char, usize, usize),
}
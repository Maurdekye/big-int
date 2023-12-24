#[cfg(test)]
mod tests {

    use big_int::*;
    use std::str::FromStr;
    use rand::prelude::*;

    #[test]
    fn parse() {
        assert_eq!("125".parse(), Ok(BigInt::<10>::from(125)));
        assert_eq!("-500".parse(), Ok(BigInt::<10>::from(-500)));
        assert_eq!("0".parse(), Ok(BigInt::<10>::from(0)));
        assert_eq!(
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".parse(),
        Ok(BigInt::<10>(false, vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    }

    #[test]
    fn parse_error() {
        assert_eq!(
            BigInt::<10>::from_str(""),
            Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
        );
        assert_eq!(
            BigInt::<10>::from_str("-"),
            Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
        );
        assert_eq!(
            BigInt::<10>::from_str("5B"),
            Err(BigIntError::ParseFailed(ParseError::DigitTooLarge(
                'B', 11, 10
            )))
        );
        assert_eq!(
            BigInt::<10>::from_str("13_4"),
            Err(BigIntError::ParseFailed(ParseError::UnrecognizedCharacter(
                '_'
            )))
        );
    }

    #[test]
    fn from_primitive() {
        assert_eq!(BigInt::<10>::from(524_u128), BigInt(false, vec![5, 2, 4]));
        assert_eq!(BigInt::<10>::from(-301_isize), BigInt(true, vec![3, 0, 1]));
        assert_eq!(BigInt::<10>::from(255_u8), BigInt(false, vec![2, 5, 5]));
    }

    #[test]
    fn normalize() {
        assert_eq!(
            BigInt::<10>(false, vec![0, 0, 0, 0]).normalized(),
            BigInt(false, vec![0])
        );
        assert_eq!(
            BigInt::<10>(true, vec![0, 0]).normalized(),
            BigInt(false, vec![0])
        );
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
    fn fuzzy_addition_test() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::<10>::from(a + b),
                BigInt::from(a) + BigInt::from(b),
                "{a} + {b}"
            );
        }
    }

    #[test]
    fn subtraction() {
        let a = BigInt::<10>::from(55);
        let b = BigInt::from(14);
        assert_eq!(a - b, BigInt::from(41));
    }

    #[test]
    fn subtraction_2() {
        let a = BigInt::<10>::from(27792);
        let b = BigInt::from(27792);
        assert_eq!(a - b, BigInt::from(0));
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
    fn fuzzy_subtraction_test() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::<10>::from(a - b),
                BigInt::from(a) - BigInt::from(b),
                "{a} - {b}"
            );
        }
    }

    #[test]
    fn multiplication() {
        let a = BigInt::<10>::from(13);
        let b = BigInt::from(5);
        assert_eq!(a * b, BigInt::from(65));
    }

    #[test]
    fn big_multiplication() {
        let a = BigInt::<10>::from(356432214);
        let b = BigInt::from(499634);
        assert_eq!(a * b, BigInt::from(178085652809676_i128));
    }

    #[test]
    fn fuzzy_multiplication_test() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::<10>::from(a * b),
                BigInt::from(a) * BigInt::from(b),
                "{a} * {b}"
            );
        }
    }

    #[test]
    fn division() {
        let a = BigInt::<10>::from(999_999_999);
        let b = BigInt::from(56_789);
        assert_eq!(
            a.div_rem(b),
            Ok((BigInt::from(17_609), BigInt::from(2_498)))
        );
    }

    #[test]
    fn division_2() {
        let a = BigInt::<10>::from(-25106);
        let b = BigInt::from(6331);
        assert_eq!(a.div_rem(b), Ok((BigInt::from(-3), BigInt::from(-6113))));
    }

    #[test]
    fn division_3() {
        let a = BigInt::<10>::from(-27792);
        let b = BigInt::from(6);
        assert_eq!(a.div_rem(b), Ok((BigInt::from(-4632), BigInt::from(0))));
    }

    #[test]
    fn division_4() {
        let a = BigInt::<256>::from(6689728775289925438_u128);
        let b = BigInt::from(3680976435299388678_u128);
        assert_eq!(a.div_rem(b), Ok((BigInt(false, vec![1]), BigInt(false, vec![41, 193, 60, 79, 234, 66, 226, 56]))));
    }

    #[test]
    fn division_by_zero() {
        let a = BigInt::<10>::from(999_999_999);
        let b = BigInt::from(0);
        assert_eq!(a.div_rem(b), Err(BigIntError::DivisionByZero));
    }

    #[test]
    fn fuzzy_division_test() {
        for _ in 0..100_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem(BigInt::from(b)),
                    Ok((BigInt::<10>::from(a / b), BigInt::<10>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_256_division_test() {
        for _ in 0..100_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem(BigInt::from(b)),
                    Ok((BigInt::<256>::from(a / b), BigInt::<256>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_div_rem_2_test() {
        for _ in 0..100_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem_2(BigInt::from(b)),
                    Ok((BigInt::<10>::from(a / b), BigInt::<10>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_256_div_rem_2_test() {
        for _ in 0..100_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem_2(BigInt::from(b)),
                    Ok((BigInt::<256>::from(a / b), BigInt::<256>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_2_tests() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::from(a) + BigInt::from(b),
                BigInt::<2>::from(a + b),
                "{a} * {b}"
            );
            assert_eq!(
                BigInt::from(a) - BigInt::from(b),
                BigInt::<2>::from(a - b),
                "{a} - {b}"
            );
            assert_eq!(
                BigInt::from(a) * BigInt::from(b),
                BigInt::<2>::from(a * b),
                "{a} * {b}"
            );
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem(BigInt::from(b)),
                    Ok((BigInt::<2>::from(a / b), BigInt::<2>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_16_tests() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::from(a) + BigInt::from(b),
                BigInt::<16>::from(a + b),
                "{a} * {b}"
            );
            assert_eq!(
                BigInt::from(a) - BigInt::from(b),
                BigInt::<16>::from(a - b),
                "{a} - {b}"
            );
            assert_eq!(
                BigInt::from(a) * BigInt::from(b),
                BigInt::<16>::from(a * b),
                "{a} * {b}"
            );
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem(BigInt::from(b)),
                    Ok((BigInt::<16>::from(a / b), BigInt::<16>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_64_tests() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::from(a) + BigInt::from(b),
                BigInt::<64>::from(a + b),
                "{a} * {b}"
            );
            assert_eq!(
                BigInt::from(a) - BigInt::from(b),
                BigInt::<64>::from(a - b),
                "{a} - {b}"
            );
            assert_eq!(
                BigInt::from(a) * BigInt::from(b),
                BigInt::<64>::from(a * b),
                "{a} * {b}"
            );
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem(BigInt::from(b)),
                    Ok((BigInt::<64>::from(a / b), BigInt::<64>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_256_tests() {
        for _ in 0..10_000 {
            let a = random::<i64>() as i128;
            let b = random::<i64>() as i128;
            assert_eq!(
                BigInt::from(a) + BigInt::from(b),
                BigInt::<256>::from(a + b),
                "{a} * {b}"
            );
            assert_eq!(
                BigInt::from(a) - BigInt::from(b),
                BigInt::<256>::from(a - b),
                "{a} - {b}"
            );
            assert_eq!(
                BigInt::from(a) * BigInt::from(b),
                BigInt::<256>::from(a * b),
                "{a} * {b}"
            );
            if b > 0 {
                assert_eq!(
                    BigInt::from(a).div_rem(BigInt::from(b)),
                    Ok((BigInt::<256>::from(a / b), BigInt::<256>::from(a % b))),
                    "{a} / {b}"
                );
            }
        }
    }
}

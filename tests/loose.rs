#[cfg(test)]
mod tests {

    use big_int::{
        base64::{encode, decode},
        error::{BigIntError, ParseError}, loose::{LooseInt, Loose}, BigInt, BigIntImplementation,
    };
    use rand::prelude::*;
    use std::str::FromStr;

    #[test]
    fn parse() {
        assert_eq!("125".parse(), Ok(LooseInt::<10>::from(125)));
        assert_eq!("-500".parse(), Ok(LooseInt::<10>::from(-500)));
        assert_eq!("0".parse(), Ok(LooseInt::<10>::from(0)));
        assert_eq!(
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".parse(),
        Ok(BigInt(unsafe { Loose::<10>::from_raw_parts(vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) })))
    }

    #[test]
    fn parse_error() {
        assert_eq!(
            LooseInt::<10>::from_str(""),
            Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
        );
        assert_eq!(
            LooseInt::<10>::from_str("-"),
            Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
        );
        assert_eq!(
            LooseInt::<10>::from_str("5B"),
            Err(BigIntError::ParseFailed(ParseError::DigitTooLarge(
                'B', 11, 10
            )))
        );
        assert_eq!(
            LooseInt::<10>::from_str("13_4"),
            Err(BigIntError::ParseFailed(ParseError::UnrecognizedCharacter(
                '_'
            )))
        );
    }

    #[test]
    fn from_primitive() {
        assert_eq!(LooseInt::<10>::from(524_u128), BigInt(unsafe {
            Loose::from_raw_parts(vec![5, 2, 4])
        }));
        assert_eq!(LooseInt::<10>::from(-301_isize), -BigInt(unsafe {
            Loose::from_raw_parts(vec![3, 0, 1])
        }));
        assert_eq!(LooseInt::<10>::from(255_u8), BigInt(unsafe {
            Loose::from_raw_parts(vec![2, 5, 5])
        }));
    }

    #[test]
    fn normalized() {
        assert_eq!(
            BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 0, 0]) }).normalized(),
            0.into()
        );
        assert_eq!(
            -BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0]) }).normalized(),
            0.into()
        );
        assert_eq!(
            BigInt(unsafe { Loose::<10>::from_raw_parts(vec![]) }).normalized(),
            0.into()
        );
        assert_eq!(
            BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) }).normalized(),
            83.into()
        );
    }

    #[test]
    fn normalize() {
        let mut n = BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 0, 0]) });
        n.normalize();
        assert_eq!(n, 0.into());
        let mut n = -BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0]) });
        n.normalize();
        assert_eq!(n, 0.into());
        let mut n = BigInt(unsafe { Loose::<10>::from_raw_parts(vec![]) });
        n.normalize();
        assert_eq!(n, 0.into());
        let mut n = BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) });
        n.normalize();
        assert_eq!(n, 83.into());
    }

    #[test]
    fn addition() {
        let a: LooseInt<10> = 100.into();
        let b = 21.into();
        assert_eq!(a + b, 121.into());
    }

    #[test]
    fn addition_with_carry() {
        let a: LooseInt<10> = 15.into();
        let b = 6.into();
        assert_eq!(a + b, 21.into());
    }

    #[test]
    fn addition_with_many_carries() {
        let a: LooseInt<10> = 99999.into();
        let b = 1.into();
        assert_eq!(a + b, 100000.into());
    }

    #[test]
    fn addition_base_16() {
        let a: LooseInt<16> = "8".parse().unwrap();
        let b = "A".parse().unwrap();
        assert_eq!(a + b, "12".parse().unwrap());
    }

    #[test]
    fn fuzzy_addition_test() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(
                LooseInt::<10>::from(a + b),
                LooseInt::from(a) + LooseInt::from(b),
                "{a} + {b}"
            );
        }
    }

    #[test]
    fn fuzzy_addassign_test() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a_ = rng.gen::<i64>() as i128;
            let b_ = rng.gen::<i64>() as i128;
            let a: LooseInt<10> = a_.into();
            let b: LooseInt<10> = b_.into();
            let mut c = a.clone();
            c += b.clone();
            assert_eq!(a + b, c, "{a_} += {b_}");
        }
    }

    #[test]
    fn subtraction() {
        let a: LooseInt<10> = 55.into();
        let b = 14.into();
        assert_eq!(a - b, 41.into());
    }

    #[test]
    fn subtraction_2() {
        let a: LooseInt<10> = 27792.into();
        let b = 27792.into();
        assert_eq!(a - b, 0.into());
    }

    #[test]
    fn subtraction_with_borrow() {
        let a: LooseInt<10> = 12.into();
        let b = 4.into();
        assert_eq!(a - b, 8.into());
    }

    #[test]
    fn subtraction_with_many_borrows() {
        let a: LooseInt<10> = 100000.into();
        let b = 1.into();
        assert_eq!(a - b, 99999.into());
    }

    #[test]
    fn subtraction_with_overflow() {
        let a: LooseInt<10> = 50.into();
        let b = 75.into();
        assert_eq!(a - b, (-25).into());
    }

    #[test]
    fn fuzzy_subtraction_test() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(
                LooseInt::<10>::from(a - b),
                LooseInt::from(a) - LooseInt::from(b),
                "{a} - {b}"
            );
        }
    }

    #[test]
    fn fuzzy_subassign_test() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a_ = rng.gen::<i64>() as i128;
            let b_ = rng.gen::<i64>() as i128;
            let a: LooseInt<10> = a_.into();
            let b: LooseInt<10> = b_.into();
            let mut c = a.clone();
            c -= b.clone();
            assert_eq!(a - b, c, "{a_} -= {b_}");
        }
    }

    #[test]
    fn multiplication() {
        let a: LooseInt<10> = 13.into();
        let b = 5.into();
        assert_eq!(a * b, 65.into());
    }

    #[test]
    fn big_multiplication() {
        let a: LooseInt<10> = 356432214.into();
        let b = 499634.into();
        assert_eq!(a * b, 178085652809676_i128.into());
    }

    #[test]
    fn fuzzy_multiplication_test() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(
                LooseInt::<10>::from(a * b),
                LooseInt::from(a) * LooseInt::from(b),
                "{a} * {b}"
            );
        }
    }

    #[test]
    fn division() {
        let a: LooseInt<10> = 999_999_999.into();
        let b = 56_789.into();
        assert_eq!(a.div_rem(b), Ok((17_609.into(), 2_498.into())));
    }

    #[test]
    fn division_2() {
        let a: LooseInt<10> = (-25106).into();
        let b = 6331.into();
        assert_eq!(a.div_rem(b), Ok(((-3).into(), (-6113).into())));
    }

    #[test]
    fn division_3() {
        let a: LooseInt<10> = (-27792).into();
        let b = 6.into();
        assert_eq!(a.div_rem(b), Ok(((-4632).into(), 0.into())));
    }

    #[test]
    fn division_4() {
        let a: LooseInt<256> = 6689728775289925438_u128.into();
        let b = 3680976435299388678_u128.into();
        assert_eq!(
            a.div_rem(b),
            Ok((BigInt(unsafe { Loose::from_raw_parts(vec![1]) }), BigInt(unsafe {
                Loose::from_raw_parts(vec![41, 193, 60, 79, 234, 66, 226, 56])
            }),))
        );
    }

    #[test]
    fn division_5() {
        let a = 30997532758381152_usize;
        let b = 16;
        assert_eq!(
            Ok((LooseInt::<10>::from(a / b), (a % b).into())),
            LooseInt::from(a).div_rem(b.into())
        );
    }

    #[test]
    fn division_by_zero() {
        let a: LooseInt<10> = 999_999_999.into();
        let b = 0.into();
        assert_eq!(a.div_rem(b), Err(BigIntError::DivisionByZero));
    }

    #[test]
    fn fuzzy_div_rem_2_test() {
        let mut rng = thread_rng();
        for _ in 0..100_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            if b > 0 {
                assert_eq!(
                    LooseInt::<10>::from(a).div_rem(b.into()),
                    Ok(((a / b).into(), (a % b).into())),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_256_div_rem_2_test() {
        let mut rng = thread_rng();
        for _ in 0..100_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            if b > 0 {
                assert_eq!(
                    LooseInt::<256>::from(a).div_rem(b.into()),
                    Ok(((a / b).into(), (a % b).into())),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn fuzzy_base_2_tests() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<2>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
            assert_eq!(LooseInt::<2>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
            assert_eq!(LooseInt::<2>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
            if b > 0 {
                assert_eq!(LooseInt::<2>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
            }
        }
    }

    #[test]
    fn fuzzy_base_16_tests() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<16>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
            assert_eq!(LooseInt::<16>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
            assert_eq!(LooseInt::<16>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
            if b > 0 {
                assert_eq!(LooseInt::<16>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
            }
        }
    }

    #[test]
    fn fuzzy_base_64_tests() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<64>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
            assert_eq!(LooseInt::<64>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
            assert_eq!(LooseInt::<64>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
            if b > 0 {
                assert_eq!(LooseInt::<64>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
            }
        }
    }

    #[test]
    fn fuzzy_base_256_tests() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let a = rng.gen::<i64>() as i128;
            let b = rng.gen::<i64>() as i128;
            assert_eq!(
                LooseInt::<256>::from(a) + b.into(),
                (a + b).into(),
                "{a} + {b}"
            );
            assert_eq!(
                LooseInt::<256>::from(a) - b.into(),
                (a - b).into(),
                "{a} - {b}"
            );
            assert_eq!(
                LooseInt::<256>::from(a) * b.into(),
                (a * b).into(),
                "{a} * {b}"
            );
            if b > 0 {
                assert_eq!(
                    LooseInt::<256>::from(a) / b.into(),
                    (a / b).into(),
                    "{a} / {b}"
                );
            }
        }
    }

    #[test]
    fn conversion_test() {
        assert_eq!(LooseInt::<10>::from(99825).convert(), LooseInt::<16>::from(99825));
    }

    #[test]
    fn conversion_test_2() {
        assert_eq!(
            LooseInt::<10>::from(-7935368386145574994_isize).convert(),
            LooseInt::<16>::from(-7935368386145574994_isize)
        );
    }

    #[test]
    fn fuzzy_conversion_test_10_to_16() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let n = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<10>::from(n).convert(), LooseInt::<16>::from(n), "{n}")
        }
    }

    #[test]
    fn fuzzy_conversion_test_2_to_10() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let n = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<2>::from(n).convert(), LooseInt::<10>::from(n), "{n}")
        }
    }

    #[test]
    fn fuzzy_conversion_test_27_to_64() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let n = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<27>::from(n).convert(), LooseInt::<64>::from(n), "{n}")
        }
    }

    #[test]
    fn fuzzy_conversion_test_10_to_256() {
        let mut rng = thread_rng();
        for _ in 0..10_000 {
            let n = rng.gen::<i64>() as i128;
            assert_eq!(LooseInt::<10>::from(n).convert(), LooseInt::<256>::from(n), "{n}")
        }
    }

    #[test]
    fn shl() {
        assert_eq!(LooseInt::<10>::from(15) << 1.into(), 150.into());
        assert_eq!(LooseInt::<2>::from(41) << 1.into(), 82.into());
        assert_eq!(LooseInt::<32>::from(7) << 3.into(), 229376.into());
    }

    #[test]
    fn shr() {
        assert_eq!(LooseInt::<10>::from(9100) >> 2.into(), 91.into());
        assert_eq!(LooseInt::<2>::from(256) >> 4.into(), 16.into());
        assert_eq!(LooseInt::<16>::from(28672) >> 3.into(), 7.into());
    }

    #[test]
    fn base64_encode_test() {
        let data = b"Hello world!";
        assert_eq!(encode(data), "SGVsbG8gd29ybGQh");
    }

    #[test]
    fn base64_decode_test() {
        let string = "SGVsbG8gd29ybGQh";
        assert_eq!(decode(string).unwrap(), b"Hello world!");
    }
}

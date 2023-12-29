use big_int::{
    error::{BigIntError, ParseError},
    prelude::*,
    test_pairs, test_values,
};
use rand::prelude::*;
use std::str::FromStr;

#[test]
fn parse() {
    assert_eq!("125".parse(), Ok(TightInt::<10>::from(125)));
    assert_eq!("-500".parse(), Ok(TightInt::<10>::from(-500)));
    assert_eq!("0".parse(), Ok(TightInt::<10>::from(0)));
    assert_eq!(
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".parse(),
        Ok(TightInt::<10>::from(vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
}

#[test]
fn parse_error() {
    assert_eq!(
        TightInt::<10>::from_str(""),
        Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
    );
    assert_eq!(
        TightInt::<10>::from_str("-"),
        Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
    );
    assert_eq!(
        TightInt::<10>::from_str("5B"),
        Err(BigIntError::ParseFailed(ParseError::DigitTooLarge(
            'B', 11, 10
        )))
    );
    assert_eq!(
        TightInt::<10>::from_str("13_4"),
        Err(BigIntError::ParseFailed(ParseError::UnrecognizedCharacter(
            '_'
        )))
    );
}

#[test]
fn from_primitive() {
    assert_eq!(
        TightInt::<10>::from(524_u128),
        vec![5, 2, 4].into()
    );
    assert_eq!(
        TightInt::<10>::from(-301_isize),
        -TightInt::from(vec![3, 0, 1])
    );
    assert_eq!(
        TightInt::<10>::from(255_u8),
        vec![2, 5, 5].into()
    );
}

#[test]
fn normalized() {
    assert_eq!(
        TightInt::<10>::from(vec![0, 0, 0, 0]).normalized(),
        0.into()
    );
    assert_eq!(
        (-TightInt::<10>::from(vec![0, 0])).normalized(),
        0.into()
    );
    assert_eq!(
        TightInt::<10>::from(vec![]).normalized(),
        0.into()
    );
    assert_eq!(
        TightInt::<10>::from(vec![0, 0, 8, 3]).normalized(),
        83.into()
    );
}

#[test]
fn normalize() {
    let mut n = TightInt::<10>::from(vec![0, 0, 0, 0]);
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = -TightInt::<10>::from(vec![0, 0]);
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = TightInt::<10>::from(vec![]);
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = TightInt::<10>::from(vec![0, 0, 8, 3]);
    n.normalize();
    assert_eq!(n, 83.into());
}

#[test]
fn addition() {
    let a: TightInt<10> = 100.into();
    let b = 21.into();
    assert_eq!(a + b, 121.into());
}

#[test]
fn addition_2() {
    let a: TightInt<10> = (-26).into();
    let b = 93.into();
    assert_eq!(a + b, 67.into());
}

#[test]
fn addition_3() {
    let a: TightInt<10> = (-58).into();
    let b = 110.into();
    assert_eq!(a + b, 52.into());
}

#[test]
fn addition_4() {
    let mut a: TightInt<10> = 1.into();
    let b = 108.into();
    a += b;
    assert_eq!(a, 109.into());
}

#[test]
fn addition_with_carry() {
    let a: TightInt<10> = 15.into();
    let b = 6.into();
    assert_eq!(a + b, 21.into());
}

#[test]
fn addition_with_many_carries() {
    let a: TightInt<10> = 99999.into();
    let b = 1.into();
    assert_eq!(a + b, 100000.into());
}

#[test]
fn addition_base_16() {
    let a: TightInt<16> = "8".parse().unwrap();
    let b = "A".parse().unwrap();
    assert_eq!(a + b, "12".parse().unwrap());
}

#[test]
fn fuzzy_addition_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<10>::from(a + b),
            TightInt::from(a) + TightInt::from(b),
            "{a} + {b}"
        );
    }
}

#[test]
fn fuzzy_addassign_test() {
    for (a_, b_) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: TightInt<10> = a_.into();
        let b: TightInt<10> = b_.into();
        let mut c = a.clone();
        c += b.clone();
        assert_eq!(a + b, c, "{a_} += {b_}");
    }
}

#[test]
fn subtraction() {
    let a: TightInt<10> = 55.into();
    let b = 14.into();
    assert_eq!(a - b, 41.into());
}

#[test]
fn subtraction_2() {
    let a: TightInt<10> = 27792.into();
    let b = 27792.into();
    assert_eq!(a - b, 0.into());
}

#[test]
fn subtraction_3() {
    let a: TightInt<10> = (-110).into();
    let b = (-58).into();
    assert_eq!(a - b, (-52).into());
}

#[test]
fn subtraction_with_borrow() {
    let a: TightInt<10> = 12.into();
    let b = 4.into();
    assert_eq!(a - b, 8.into());
}

#[test]
fn subtraction_with_many_borrows() {
    let a: TightInt<10> = 100000.into();
    let b = 1.into();
    assert_eq!(a - b, 99999.into());
}

#[test]
fn subtraction_with_overflow() {
    let a: TightInt<10> = 50.into();
    let b = 75.into();
    assert_eq!(a - b, (-25).into());
}

#[test]
fn fuzzy_subtraction_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<10>::from(a - b),
            TightInt::from(a) - TightInt::from(b),
            "{a} - {b}"
        );
    }
}

#[test]
fn fuzzy_subassign_test() {
    for (a_, b_) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: TightInt<10> = a_.into();
        let b: TightInt<10> = b_.into();
        let mut c = a.clone();
        c -= b.clone();
        assert_eq!(a - b, c, "{a_} -= {b_}");
    }
}

#[test]
fn multiplication() {
    let a: TightInt<10> = 13.into();
    let b = 5.into();
    assert_eq!(a * b, 65.into());
}

#[test]
fn big_multiplication() {
    let a: TightInt<10> = 356432214.into();
    let b = 499634.into();
    assert_eq!(a * b, 178085652809676_i128.into());
}

#[test]
fn fuzzy_multiplication_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<10>::from(a * b),
            TightInt::from(a) * TightInt::from(b),
            "{a} * {b}"
        );
    }
}

#[test]
fn division() {
    let a: TightInt<10> = 999_999_999.into();
    let b = 56_789.into();
    assert_eq!(a.div_rem(b), Ok((17_609.into(), 2_498.into())));
}

#[test]
fn division_2() {
    let a: TightInt<10> = (-25106).into();
    let b = 6331.into();
    assert_eq!(a.div_rem(b), Ok(((-3).into(), (-6113).into())));
}

#[test]
fn division_3() {
    let a: TightInt<10> = (-27792).into();
    let b = 6.into();
    assert_eq!(a.div_rem(b), Ok(((-4632).into(), 0.into())));
}

#[test]
fn division_5() {
    let a = 30997532758381152_usize;
    let b = 16;
    assert_eq!(
        Ok((TightInt::<10>::from(a / b), (a % b).into())),
        TightInt::from(a).div_rem(b.into())
    );
}

#[test]
fn division_6() {
    let a = 10;
    let b = 2;
    assert_eq!(
        Ok((TightInt::<10>::from(a / b), (a % b).into())),
        TightInt::from(a).div_rem(b.into())
    );
}

#[test]
fn division_7() {
    let a = -11;
    let b = 79;
    assert_eq!(
        Ok((TightInt::<256>::from(a / b), (a % b).into())),
        TightInt::from(a).div_rem(b.into())
    );
}

#[test]
fn division_by_zero() {
    let a: TightInt<10> = 999_999_999.into();
    let b = 0.into();
    assert_eq!(a.div_rem(b), Err(BigIntError::DivisionByZero));
}

#[test]
fn fuzzy_div_rem_2_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        if b > 0 {
            assert_eq!(
                TightInt::<10>::from(a).div_rem(b.into()),
                Ok(((a / b).into(), (a % b).into())),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_256_div_rem_2_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        if b > 0 {
            assert_eq!(
                TightInt::<256>::from(a).div_rem(b.into()),
                Ok(((a / b).into(), (a % b).into())),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_2_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<2>::from(a) + b.into(),
            (a + b).into(),
            "{a} + {b}"
        );
        assert_eq!(
            TightInt::<2>::from(a) - b.into(),
            (a - b).into(),
            "{a} - {b}"
        );
        assert_eq!(
            TightInt::<2>::from(a) * b.into(),
            (a * b).into(),
            "{a} * {b}"
        );
        if b > 0 {
            assert_eq!(
                TightInt::<2>::from(a) / b.into(),
                (a / b).into(),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_16_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<16>::from(a) + b.into(),
            (a + b).into(),
            "{a} + {b}"
        );
        assert_eq!(
            TightInt::<16>::from(a) - b.into(),
            (a - b).into(),
            "{a} - {b}"
        );
        assert_eq!(
            TightInt::<16>::from(a) * b.into(),
            (a * b).into(),
            "{a} * {b}"
        );
        if b > 0 {
            assert_eq!(
                TightInt::<16>::from(a) / b.into(),
                (a / b).into(),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_64_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<64>::from(a) + b.into(),
            (a + b).into(),
            "{a} + {b}"
        );
        assert_eq!(
            TightInt::<64>::from(a) - b.into(),
            (a - b).into(),
            "{a} - {b}"
        );
        assert_eq!(
            TightInt::<64>::from(a) * b.into(),
            (a * b).into(),
            "{a} * {b}"
        );
        if b > 0 {
            assert_eq!(
                TightInt::<64>::from(a) / b.into(),
                (a / b).into(),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_256_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<256>::from(a) + b.into(),
            (a + b).into(),
            "{a} + {b}"
        );
        assert_eq!(
            TightInt::<256>::from(a) - b.into(),
            (a - b).into(),
            "{a} - {b}"
        );
        assert_eq!(
            TightInt::<256>::from(a) * b.into(),
            (a * b).into(),
            "{a} * {b}"
        );
        if b > 0 {
            assert_eq!(
                TightInt::<256>::from(a) / b.into(),
                (a / b).into(),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn conversion_test() {
    assert_eq!(
        TightInt::<10>::from(99825).convert(),
        TightInt::<16>::from(99825)
    );
}

#[test]
fn conversion_test_2() {
    assert_eq!(
        TightInt::<10>::from(-7935368386145574994_isize).convert(),
        TightInt::<16>::from(-7935368386145574994_isize)
    );
}

#[test]
fn fuzzy_conversion_test_10_to_16() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<10>::from(n).convert(),
            TightInt::<16>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_conversion_test_2_to_10() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<2>::from(n).convert(),
            TightInt::<10>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_conversion_test_27_to_64() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<27>::from(n).convert(),
            TightInt::<64>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_conversion_test_10_to_256() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<10>::from(n).convert(),
            TightInt::<256>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_comparison_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            TightInt::<10>::from(a).cmp(&b.into()),
            a.cmp(&b),
            "{a} <> {b}"
        )
    }
}

#[test]
fn shl() {
    assert_eq!(TightInt::<10>::from(15) << 1.into(), 150.into());
    assert_eq!(TightInt::<2>::from(41) << 1.into(), 82.into());
    assert_eq!(TightInt::<32>::from(7) << 3.into(), 229376.into());
}

#[test]
fn shr() {
    assert_eq!(TightInt::<10>::from(9100) >> 2.into(), 91.into());
    assert_eq!(TightInt::<2>::from(256) >> 4.into(), 16.into());
    assert_eq!(TightInt::<16>::from(28672) >> 3.into(), 7.into());
}

#[test]
fn shr_2() {
    let a = TightInt::<10>::from(9100);
    let b = 91.into();
    assert_eq!(a.shr(2), b);
}

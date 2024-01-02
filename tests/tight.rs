use big_int::{
    error::{BigIntError, ParseError},
    prelude::*,
    test_pairs, test_values,
};
use std::str::FromStr;
use std::ops::AddAssign;

#[test]
fn parse() {
    assert_eq!("125".parse(), Ok(Tight::<10>::from(125)));
    assert_eq!("-500".parse(), Ok(Tight::<10>::from(-500)));
    assert_eq!("0".parse(), Ok(Tight::<10>::from(0)));
    assert_eq!(
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".parse(),
        Ok(vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].into_iter().collect::<Tight<10>>()))
}

#[test]
fn parse_error() {
    assert_eq!(
        Tight::<10>::from_str(""),
        Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
    );
    assert_eq!(
        Tight::<10>::from_str("-"),
        Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
    );
    assert_eq!(
        Tight::<10>::from_str("5B"),
        Err(BigIntError::ParseFailed(ParseError::DigitTooLarge(
            'B', 11, 10
        )))
    );
    assert_eq!(
        Tight::<10>::from_str("13_4"),
        Err(BigIntError::ParseFailed(ParseError::UnrecognizedCharacter(
            '_'
        )))
    );
}

#[test]
fn from_primitive() {
    assert_eq!(
        Tight::<10>::from(524_u128),
        vec![5, 2, 4].into_iter().collect()
    );
    assert_eq!(
        Tight::<10>::from(-301_isize),
        -vec![3, 0, 1].into_iter().collect::<Tight<10>>()
    );
    assert_eq!(
        Tight::<10>::from(255_u8),
        vec![2, 5, 5].into_iter().collect()
    );
}

#[test]
fn normalized() {
    assert_eq!(
        unsafe { Tight::<10>::from_raw_parts(vec![0, 0, 0, 0].into(), 16, 32) }.normalized(),
        0.into()
    );
    assert_eq!(
        (-unsafe { Tight::<10>::from_raw_parts(vec![0, 0].into(), 4, 12) }).normalized(),
        0.into()
    );
    assert_eq!(
        unsafe { Tight::<10>::from_raw_parts(vec![].into(), 0, 0) }.normalized(),
        0.into()
    );
    assert_eq!(
        unsafe { Tight::<10>::from_raw_parts(vec![0b0000_0000, 0b1000_0011].into(), 8, 16) }
            .normalized(),
        83.into()
    );
}

#[test]
fn normalize() {
    let mut n = Tight::<10>::from(vec![0, 0, 0, 0]);
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = -Tight::<10>::from(vec![0, 0]);
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = Tight::<10>::from(vec![]);
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = Tight::<10>::from(vec![0, 0, 8, 3]);
    n.normalize();
    assert_eq!(n, 83.into());
}

#[test]
fn addition() {
    let a: Tight<10> = 100.into();
    let b = 21.into();
    assert_eq!(a + b, 121.into());
}

#[test]
fn addition_2() {
    let a: Tight<10> = (-26).into();
    let b = 93.into();
    assert_eq!(a + b, 67.into());
}

#[test]
fn addition_3() {
    let a: Tight<10> = (-58).into();
    let b = 110.into();
    assert_eq!(a + b, 52.into());
}

#[test]
fn addition_4() {
    let mut a: Tight<10> = 1.into();
    let b = 108.into();
    a += b;
    assert_eq!(a, 109.into());
}

#[test]
fn addition_5() {
    let mut a: Tight<10> = (-5).into();
    let b: Tight<10> = 0.into();
    a.add_assign(b);
    assert_eq!(a, (-5).into());
}

#[test]
fn addition_with_carry() {
    let a: Tight<10> = 15.into();
    let b = 6.into();
    assert_eq!(a + b, 21.into());
}

#[test]
fn addition_with_many_carries() {
    let a: Tight<10> = 99999.into();
    let b = 1.into();
    assert_eq!(a + b, 100000.into());
}

#[test]
fn addition_base_16() {
    let a: Tight<16> = "8".parse().unwrap();
    let b = "A".parse().unwrap();
    assert_eq!(a + b, "12".parse().unwrap());
}

#[test]
fn fuzzy_addition_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Tight::<10>::from(a + b),
            Tight::from(a) + Tight::from(b),
            "{a} + {b}"
        );
    }
}

#[test]
fn fuzzy_addassign_test() {
    for (a_, b_) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Tight<10> = a_.into();
        let b: Tight<10> = b_.into();
        let mut c = a.clone();
        c += b.clone();
        assert_eq!(a + b, c, "{a_} += {b_}");
    }
}

#[test]
fn subtraction() {
    let a: Tight<10> = 55.into();
    let b = 14.into();
    assert_eq!(a - b, 41.into());
}

#[test]
fn subtraction_2() {
    let a: Tight<10> = 27792.into();
    let b = 27792.into();
    assert_eq!(a - b, 0.into());
}

#[test]
fn subtraction_3() {
    let a: Tight<10> = (-110).into();
    let b = (-58).into();
    assert_eq!(a - b, (-52).into());
}

#[test]
fn subtraction_with_borrow() {
    let a: Tight<10> = 12.into();
    let b = 4.into();
    assert_eq!(a - b, 8.into());
}

#[test]
fn subtraction_with_many_borrows() {
    let a: Tight<10> = 100000.into();
    let b = 1.into();
    assert_eq!(a - b, 99999.into());
}

#[test]
fn subtraction_with_overflow() {
    let a: Tight<10> = 50.into();
    let b = 75.into();
    assert_eq!(a - b, (-25).into());
}

#[test]
fn fuzzy_subtraction_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Tight::<10>::from(a - b),
            Tight::from(a) - Tight::from(b),
            "{a} - {b}"
        );
    }
}

#[test]
fn fuzzy_subassign_test() {
    for (a_, b_) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Tight<10> = a_.into();
        let b: Tight<10> = b_.into();
        let mut c = a.clone();
        c -= b.clone();
        assert_eq!(a - b, c, "{a_} -= {b_}");
    }
}

#[test]
fn multiplication() {
    let a: Tight<10> = 13.into();
    let b = 5.into();
    assert_eq!(a * b, 65.into());
}

#[test]
fn big_multiplication() {
    let a: Tight<10> = 356432214.into();
    let b = 499634.into();
    assert_eq!(a * b, 178085652809676_i128.into());
}

#[test]
fn fuzzy_multiplication_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Tight::<10>::from(a * b),
            Tight::from(a) * Tight::from(b),
            "{a} * {b}"
        );
    }
}

#[test]
fn division() {
    let a: Tight<10> = 999_999_999.into();
    let b: Tight<10> = 56_789.into();
    assert_eq!(
        a.div_rem_inner::<_, Tight<10>>(b),
        Ok((17_609.into(), 2_498.into()))
    );
}

#[test]
fn division_2() {
    let a: Tight<10> = (-25106).into();
    let b: Tight<10> = 6331.into();
    assert_eq!(
        a.div_rem_inner::<_, Tight<10>>(b),
        Ok(((-3).into(), (-6113).into()))
    );
}

#[test]
fn division_3() {
    let a: Tight<10> = (-27792).into();
    let b: Tight<10> = 6.into();
    assert_eq!(a.div_rem::<_, Tight<10>>(b), Ok(((-4632).into(), 0.into())));
}

#[test]
fn division_5() {
    let a = 30997532758381152_usize;
    let b = 16;
    assert_eq!(
        Ok((Tight::<10>::from(a / b), (a % b).into())),
        Tight::from(a).div_rem::<Tight<10>, Tight<10>>(b.into())
    );
}

#[test]
fn division_6() {
    let a = 10;
    let b = 2;
    assert_eq!(
        Ok((Tight::<10>::from(a / b), (a % b).into())),
        Tight::from(a).div_rem::<Tight<10>, Tight<10>>(b.into())
    );
}

#[test]
fn division_7() {
    let a = -11;
    let b = 79;
    assert_eq!(
        Ok((Tight::<256>::from(a / b), (a % b).into())),
        Tight::from(a).div_rem::<Tight<256>, Tight<256>>(b.into())
    );
}

#[test]
fn division_by_zero() {
    let a: Tight<10> = 999_999_999.into();
    let b: Tight<10> = 0.into();
    assert_eq!(
        a.div_rem_inner::<Tight<10>, Tight<10>>(b),
        Err(BigIntError::DivisionByZero)
    );
}

#[test]
fn fuzzy_div_rem_2_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        if b > 0 {
            assert_eq!(
                Tight::<10>::from(a).div_rem_inner::<Tight<10>, Tight<10>>(b.into()),
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
                Tight::<256>::from(a).div_rem_inner::<Tight<256>, Tight<256>>(b.into()),
                Ok(((a / b).into(), (a % b).into())),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_2_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(Tight::<2>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(Tight::<2>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(Tight::<2>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(Tight::<2>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_base_16_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(Tight::<16>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(Tight::<16>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(Tight::<16>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(Tight::<16>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_base_64_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(Tight::<64>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(Tight::<64>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(Tight::<64>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(Tight::<64>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_base_256_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Tight::<256>::from(a) + b.into(),
            (a + b).into(),
            "{a} + {b}"
        );
        assert_eq!(
            Tight::<256>::from(a) - b.into(),
            (a - b).into(),
            "{a} - {b}"
        );
        assert_eq!(
            Tight::<256>::from(a) * b.into(),
            (a * b).into(),
            "{a} * {b}"
        );
        if b > 0 {
            assert_eq!(
                Tight::<256>::from(a) / b.into(),
                (a / b).into(),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn conversion_test() {
    let a: Tight<16> = Tight::<10>::from(99825).convert();
    assert_eq!(a, Tight::<16>::from(99825));
}

#[test]
fn conversion_test_2() {
    let a: Tight<16> = Tight::<10>::from(-7935368386145574994_isize).convert();
    assert_eq!(a, Tight::<16>::from(-7935368386145574994_isize));
}

#[test]
fn fuzzy_conversion_test_10_to_16() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Tight<16> = Tight::<10>::from(n).convert();
        assert_eq!(a, n.into(), "{n}");
    }
}

#[test]
fn fuzzy_conversion_test_2_to_10() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Tight<10> = Tight::<2>::from(n).convert();
        assert_eq!(a, n.into(), "{n}");
    }
}

#[test]
fn fuzzy_conversion_test_27_to_64() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Tight<64> = Tight::<27>::from(n).convert();
        assert_eq!(a, n.into(), "{n}");
    }
}

#[test]
fn fuzzy_conversion_test_10_to_256() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Tight<16> = Tight::<10>::from(n).convert();
        assert_eq!(a, n.into(), "{n}");
    }
}

#[test]
fn fuzzy_comparison_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Tight::<10>::from(a).cmp_inner::<Tight<10>>(&b.into()),
            a.cmp(&b),
            "{a} <> {b}"
        )
    }
}

#[test]
fn shl() {
    assert_eq!(Tight::<10>::from(15) << 1.into(), 150.into());
    assert_eq!(Tight::<2>::from(41) << 1.into(), 82.into());
    assert_eq!(Tight::<32>::from(7) << 3.into(), 229376.into());
}

#[test]
fn shr() {
    assert_eq!(Tight::<10>::from(9100) >> 2.into(), 91.into());
    assert_eq!(Tight::<2>::from(256) >> 4.into(), 16.into());
    assert_eq!(Tight::<16>::from(28672) >> 3.into(), 7.into());
}

#[test]
fn shr_2() {
    let a = Tight::<10>::from(9100);
    let b = 91.into();
    assert_eq!(a.shr_inner(2), b);
}

#[test]
fn doctest() {
    let mut a: Loose<10> = "9000000000000000000000000000000000000000".parse().unwrap();
    a /= 13.into();
    assert_eq!(
        a,
        "692307692307692307692307692307692307692".parse().unwrap()
    );

    let mut b: Loose<16> = a.convert();
    assert_eq!(b, "208D59C8D8669EDC306F76344EC4EC4EC".parse().unwrap());
    b >>= 16.into();

    let c: Loose<2> = b.convert();
    assert_eq!(
        c,
        "100000100011010101100111001000110110000110011010011110110111000011"
            .parse()
            .unwrap()
    );

    let mut d: Tight<256> = c.convert();
    d += vec![15, 90, 0].into();
    assert_eq!(d, vec![2, 8, 213, 156, 141, 134, 121, 71, 195].into());

    let e: Tight<10> = d.convert();
    assert_eq!(format!("{e}"), "37530075201422313411".to_string());
}

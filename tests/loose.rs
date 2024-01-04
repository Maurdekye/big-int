use big_int::{
    error::{BigIntError, ParseError},
    prelude::*,
    test_pairs, test_values,
};
use std::str::FromStr;

#[test]
fn parse() {
    assert_eq!("125".parse(), Ok(Loose::<10>::from(125)));
    assert_eq!("-500".parse(), Ok(Loose::<10>::from(-500)));
    assert_eq!("0".parse(), Ok(Loose::<10>::from(0)));
    assert_eq!(
            "1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000".parse(),
        Ok(vec![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].into_iter().collect::<Loose<10>>())
    )
}

#[test]
fn parse_error() {
    assert_eq!(
        Loose::<10>::from_str(""),
        Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
    );
    assert_eq!(
        Loose::<10>::from_str("-"),
        Err(BigIntError::ParseFailed(ParseError::NotEnoughCharacters))
    );
    assert_eq!(
        Loose::<10>::from_str("5B"),
        Err(BigIntError::ParseFailed(ParseError::DigitTooLarge(
            'B', 11, 10
        )))
    );
    assert_eq!(
        Loose::<10>::from_str("13_4"),
        Err(BigIntError::ParseFailed(ParseError::UnrecognizedCharacter(
            '_'
        )))
    );
}

#[test]
fn from_primitive() {
    assert_eq!(
        Loose::<10>::from(524_u128),
        vec![5, 2, 4].into_iter().collect()
    );
    assert_eq!(
        Loose::<10>::from(-301_isize),
        -vec![3, 0, 1].into_iter().collect::<Loose<10>>()
    );
    assert_eq!(
        Loose::<10>::from(255_u8),
        vec![2, 5, 5].into_iter().collect()
    );
}

#[test]
fn normalized() {
    assert_eq!(
        unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 0, 0]) }.normalized(),
        0.into()
    );
    assert_eq!(
        unsafe { -Loose::<10>::from_raw_parts(vec![0, 0]) }.normalized(),
        0.into()
    );
    assert_eq!(
        unsafe { Loose::<10>::from_raw_parts(vec![]) }.normalized(),
        0.into()
    );
    assert_eq!(
        unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) }.normalized(),
        83.into()
    );
}

#[test]
fn normalize() {
    let mut n = unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 0, 0]) };
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = -unsafe { Loose::<10>::from_raw_parts(vec![0, 0]) };
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = unsafe { Loose::<10>::from_raw_parts(vec![]) };
    n.normalize();
    assert_eq!(n, 0.into());
    let mut n = unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
    n.normalize();
    assert_eq!(n, 83.into());
}

#[test]
fn addition() {
    let a: Loose<10> = 100.into();
    let b = 21.into();
    assert_eq!(a + b, 121.into());
}

#[test]
fn addition_2() {
    let a: Loose<10> = (-26).into();
    let b = 93.into();
    assert_eq!(a + b, 67.into());
}

#[test]
fn addition_3() {
    let a: Loose<10> = (-58).into();
    let b = 110.into();
    assert_eq!(a + b, 52.into());
}

#[test]
fn addition_with_carry() {
    let a: Loose<10> = 15.into();
    let b = 6.into();
    assert_eq!(a + b, 21.into());
}

#[test]
fn addition_with_many_carries() {
    let a: Loose<10> = 99999.into();
    let b = 1.into();
    assert_eq!(a + b, 100000.into());
}

#[test]
fn addition_base_16() {
    let a: Loose<16> = "8".parse().unwrap();
    let b = "A".parse().unwrap();
    assert_eq!(a + b, "12".parse().unwrap());
}

#[test]
fn fuzzy_addition_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<10>::from(a + b),
            Loose::from(a) + Loose::from(b),
            "{a} + {b}"
        );
    }
}

#[test]
fn fuzzy_addassign_test() {
    for (a_, b_) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Loose<10> = a_.into();
        let b: Loose<10> = b_.into();
        let mut c = a.clone();
        c += b.clone();
        assert_eq!(a + b, c, "{a_} += {b_}");
    }
}

#[test]
fn subtraction() {
    let a: Loose<10> = 55.into();
    let b = 14.into();
    assert_eq!(a - b, 41.into());
}

#[test]
fn subtraction_2() {
    let a: Loose<10> = 27792.into();
    let b = 27792.into();
    assert_eq!(a - b, 0.into());
}

#[test]
fn subtraction_with_borrow() {
    let a: Loose<10> = 12.into();
    let b = 4.into();
    assert_eq!(a - b, 8.into());
}

#[test]
fn subtraction_with_many_borrows() {
    let a: Loose<10> = 100000.into();
    let b = 1.into();
    assert_eq!(a - b, 99999.into());
}

#[test]
fn subtraction_with_overflow() {
    let a: Loose<10> = 50.into();
    let b = 75.into();
    assert_eq!(a - b, (-25).into());
}

#[test]
fn fuzzy_subtraction_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<10>::from(a - b),
            Loose::from(a) - Loose::from(b),
            "{a} - {b}"
        );
    }
}

#[test]
fn fuzzy_subassign_test() {
    for (a_, b_) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        let a: Loose<10> = a_.into();
        let b: Loose<10> = b_.into();
        let mut c = a.clone();
        c -= b.clone();
        assert_eq!(a - b, c, "{a_} -= {b_}");
    }
}

#[test]
fn multiplication() {
    let a: Loose<10> = 13.into();
    let b = 5.into();
    assert_eq!(a * b, 65.into());
}

#[test]
fn big_multiplication() {
    let a: Loose<10> = 356432214.into();
    let b = 499634.into();
    assert_eq!(a * b, 178085652809676_i128.into());
}

#[test]
fn fuzzy_multiplication_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<10>::from(a * b),
            Loose::from(a) * Loose::from(b),
            "{a} * {b}"
        );
    }
}

#[test]
fn division() {
    let a: Loose<10> = 999_999_999.into();
    let b: Loose<10> = 56_789.into();
    assert_eq!(
        a.div_rem_inner::<_, Loose<10>>(b),
        Ok((17_609.into(), 2_498.into()))
    );
}

#[test]
fn division_2() {
    let a: Loose<10> = (-25106).into();
    let b: Loose<10> = 6331.into();
    assert_eq!(
        a.div_rem_inner::<_, Loose<10>>(b),
        Ok(((-3).into(), (-6113).into()))
    );
}

#[test]
fn division_3() {
    let a: Loose<10> = (-27792).into();
    let b: Loose<10> = 6.into();
    let q: DenormalLoose<10> = (-4632).into();
    let rhs = Ok((q, 0.into()));
    assert_eq!(a.div_rem_inner::<_, Loose<10>>(b), rhs);
}

#[test]
fn incomprehensible_denormal_conversion_bug() {
    let n: DenormalLoose<10> = (-1).into();
    println!("{n}");
}

#[test]
fn division_4() {
    let a: Loose<256> = 6689728775289925438_u128.into();
    let b: Loose<256> = 3680976435299388678_u128.into();
    assert_eq!(
        a.div_rem(b),
        Ok((unsafe { Loose::from_raw_parts(vec![1]) }, unsafe {
            Loose::from_raw_parts(vec![41, 193, 60, 79, 234, 66, 226, 56])
        },))
    );
}

#[test]
fn division_5() {
    let a = 30997532758381152_usize;
    let b = 16;
    assert_eq!(
        Ok((Loose::<10>::from(a / b), Loose::<10>::from(a % b))),
        Loose::from(a).div_rem(Loose::<10>::from(b))
    );
}

#[test]
fn division_6() {
    let a = 10;
    let b = 2;
    assert_eq!(
        Ok((Loose::<10>::from(a / b), (a % b).into())),
        Loose::from(a).div_rem(Loose::<10>::from(b))
    );
}

#[test]
fn division_by_zero() {
    let a: Loose<10> = 999_999_999.into();
    let b: Loose<10> = 0.into();
    assert_eq!(
        a.div_rem_inner::<_, Loose<10>>(b),
        Err(BigIntError::DivisionByZero)
    );
}

#[test]
fn fuzzy_div_rem_2_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        if b > 0 {
            assert_eq!(
                Loose::<10>::from(a).div_rem_inner::<_, Loose<10>>(Loose::<10>::from(b)),
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
                Loose::<256>::from(a).div_rem_inner::<_, Loose<256>>(Loose::<256>::from(b)),
                Ok(((a / b).into(), (a % b).into())),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn fuzzy_base_2_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(Loose::<2>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(Loose::<2>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(Loose::<2>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(Loose::<2>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_base_16_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(Loose::<16>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(Loose::<16>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(Loose::<16>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(Loose::<16>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_base_64_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(Loose::<64>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(Loose::<64>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(Loose::<64>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(Loose::<64>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_base_256_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<256>::from(a) + b.into(),
            (a + b).into(),
            "{a} + {b}"
        );
        assert_eq!(
            Loose::<256>::from(a) - b.into(),
            (a - b).into(),
            "{a} - {b}"
        );
        assert_eq!(
            Loose::<256>::from(a) * b.into(),
            (a * b).into(),
            "{a} * {b}"
        );
        if b > 0 {
            assert_eq!(
                Loose::<256>::from(a) / b.into(),
                (a / b).into(),
                "{a} / {b}"
            );
        }
    }
}

#[test]
fn conversion_test() {
    assert_eq!(
        Loose::<10>::from(99825).convert::<16, Loose<16>>(),
        Loose::<16>::from(99825)
    );
}

#[test]
fn conversion_test_2() {
    assert_eq!(
        Loose::<10>::from(-7935368386145574994_isize).convert::<16, Loose<16>>(),
        Loose::<16>::from(-7935368386145574994_isize)
    );
}

#[test]
fn fuzzy_conversion_test_10_to_16() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<10>::from(n).convert::<16, Loose<16>>(),
            Loose::<16>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_conversion_test_2_to_10() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<2>::from(n).convert::<10, Loose<10>>(),
            Loose::<10>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_conversion_test_27_to_64() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<27>::from(n).convert::<64, Loose<64>>(),
            Loose::<64>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_conversion_test_10_to_256() {
    for n in test_values!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<10>::from(n).convert::<256, Loose<256>>(),
            Loose::<256>::from(n),
            "{n}"
        )
    }
}

#[test]
fn fuzzy_comparison_test() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(
            Loose::<10>::from(a).cmp_inner::<Loose<10>>(&b.into()),
            a.cmp(&b),
            "{a} <> {b}"
        )
    }
}

#[test]
fn shl() {
    assert_eq!(Loose::<10>::from(15) << 1.into(), 150.into());
    assert_eq!(Loose::<2>::from(41) << 1.into(), 82.into());
    assert_eq!(Loose::<32>::from(7) << 3.into(), 229376.into());
}

#[test]
fn shr() {
    assert_eq!(Loose::<10>::from(9100) >> 2.into(), 91.into());
    assert_eq!(Loose::<2>::from(256) >> 4.into(), 16.into());
    assert_eq!(Loose::<16>::from(28672) >> 3.into(), 7.into());
}

#[test]
fn as_iter() {
    let a: Loose<10> = 134522.into();
    let mut v = Vec::new();
    for digit in a {
        v.push(digit);
    }
    assert_eq!(v, vec![1, 3, 4, 5, 2, 2]);
}

#[test]
fn as_rev_iter() {
    let a: Loose<10> = 134522.into();
    let mut v = Vec::new();
    for digit in a.rev() {
        v.push(digit);
    }
    assert_eq!(v, vec![2, 2, 5, 4, 3, 1]);
}

#[test]
fn fuzzy_loose_bytes_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(LooseBytes::<10>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(LooseBytes::<10>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(LooseBytes::<10>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(LooseBytes::<10>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_loose_shorts_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(LooseShorts::<10>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(LooseShorts::<10>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(LooseShorts::<10>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(LooseShorts::<10>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}

#[test]
fn fuzzy_loose_words_tests() {
    for (a, b) in test_pairs!([i8; 1000], [i16; 2000], [i32; 4000], [i64; 8000]) {
        assert_eq!(LooseWords::<10>::from(a) + b.into(), (a + b).into(), "{a} + {b}");
        assert_eq!(LooseWords::<10>::from(a) - b.into(), (a - b).into(), "{a} - {b}");
        assert_eq!(LooseWords::<10>::from(a) * b.into(), (a * b).into(), "{a} * {b}");
        if b > 0 {
            assert_eq!(LooseWords::<10>::from(a) / b.into(), (a / b).into(), "{a} / {b}");
        }
    }
}
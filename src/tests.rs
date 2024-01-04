#[cfg(test)]
use big_int::prelude::*;

#[test]
fn eq() {
    let a = unsafe { Tight::<10>::from_raw_parts(vec![0b0110_0101].into(), 0, 8) };
    let b = unsafe {
        Tight::<10>::from_raw_parts(vec![0b0000_0000, 0b0011001, 0b01000000].into(), 10, 18)
    };
    assert!(a.eq_inner(&b));
}

#[test]
fn convert() {
    let n_4: Loose<4> = 78.into();
    let n_16: Loose<16> = 78.into();
    assert_eq!(n_4, n_16.convert());
}

#[test]
fn convert_2() {
    let n_4: Loose<4> = 136.into();
    let n_64: Loose<64> = 136.into();
    assert_eq!(n_4, n_64.convert());
}

#[test]
fn convert_3() {
    let n_4: Loose<4> = 29.into();
    let n_256: Loose<256> = 29.into();
    assert_eq!(n_256, n_4.convert());
}

#[test]
fn downconvert_special_cases() {
    for n in test_values!([u8; 1000], [u16; 2000], [u32; 4000], [u64; 8000]) {
        let n_4: Tight<4> = n.into();
        let n_16: Tight<16> = n.into();
        let n_64: Tight<64> = n.into();
        let n_256: Tight<256> = n.into();
        assert_eq!(n_4, n_16.clone().convert(), "{n} 16 > 4");
        assert_eq!(n_4, n_64.clone().convert(), "{n} 64 > 4");
        assert_eq!(n_4, n_256.clone().convert(), "{n} 256 > 4");
        assert_eq!(n_16, n_64.clone().convert(), "{n} 64 > 16");
        assert_eq!(n_16, n_256.clone().convert(), "{n} 256 > 16");
        assert_eq!(n_64, n_256.convert(), "{n} 256 > 64");
    }
}

#[test]
fn upconvert_special_cases() {
    for n in test_values!([u8; 1000], [u16; 2000], [u32; 4000], [u64; 8000]) {
        let n_4: Tight<4> = n.into();
        let n_16: Tight<16> = n.into();
        let n_64: Tight<64> = n.into();
        let n_256: Tight<256> = n.into();
        assert_eq!(n_256, n_4.clone().convert(), "{n} 4 > 256");
        assert_eq!(n_256, n_16.clone().convert(), "{n} 16 > 256");
        assert_eq!(n_256, n_64.clone().convert(), "{n} 64 > 256");
        assert_eq!(n_64, n_4.clone().convert(), "{n} 4 > 64");
        assert_eq!(n_64, n_16.clone().convert(), "{n} 16 > 64");
        assert_eq!(n_16, n_4.convert(), "{n} 4 > 16");
    }
}

#[test]
fn convert_special_cases_2() {
    for n in test_values!([u8; 1000], [u16; 2000], [u32; 4000], [u64; 8000]) {
        let n_10: Tight<10> = n.into();
        let n_100: Tight<100> = n.into();
        let n_27: Tight<27> = n.into();
        let n_81: Tight<81> = n.into();
        assert_eq!(n_10, n_100.clone().convert());
        assert_eq!(n_100, n_10.convert());
        assert_eq!(n_27, n_81.clone().convert());
        assert_eq!(n_81, n_27.convert());
    }
}


#[test]
fn cmp() {
    let a: Loose<10> = 106.into();
    let b: Loose<10> = (-77).into();
    assert_eq!(a.cmp_inner(&b), Ordering::Greater);
}

#[test]
fn convert_4() {
    let n = -51;
    let n_2: Loose<2> = n.into();
    let n_10: Loose<10> = n.into();
    assert_eq!(n_10, n_2.convert());
}

#[test]
fn is_power() {
    assert_eq!(big_int::is_power(10, 2), None);
}

#[test]
fn exp() {
    let a: Loose<10> = 10.into();
    let b: Loose<10> = a.exp::<Loose<10>, Loose<10>>(3.into()).unwrap();
    assert_eq!(b, 1000.into());
}

#[test]
fn exp_2() {
    let a: Loose<10> = 10.into();
    let b: Loose<10> = a.exp::<Loose<10>, Loose<10>>(20.into()).unwrap();
    assert_eq!(b, 100_000_000_000_000_000_000_u128.into());
}

#[test]
fn exp_3() {
    let a: Loose<10> = 4421.into();
    let b: Loose<10> = a.exp::<Loose<10>, Loose<10>>(19.into()).unwrap();
    assert_eq!(b, "1840304903118662555886854371754653402172820247670630063406265913840381".parse().unwrap());
}

#[test]
fn exp_4() {
    let a: Loose<10> = 216.into();
    let b: Loose<10> = a.exp::<Loose<10>, Loose<10>>(1.into()).unwrap();
    assert_eq!(b, 216.into());
}

#[test]
fn exp_5() {
    let a: Tight<10> = 180.into();
    let b: Tight<10> = a.exp::<Tight<10>, Tight<10>>(31.into()).unwrap();
    assert_eq!(b, "8193088729422601264042868660091821752320000000000000000000000000000000".parse().unwrap());
}

#[test]
fn fuzzy_exp() {
    for (a, b) in test_pairs!([i8; 100], [i16; 1000]) {
        let b = b.max(0) % 32;
        let base: Tight<10> = a.into();
        let mut result: Tight<10> = 1.into();
        for _ in 0..b {
            result *= base.clone();
        }
        assert_eq!(base.exp::<Tight<10>, Tight<10>>(b.into()).unwrap(), result, "{a} ^ {b}");
    }
}

#[test]
fn log() {
    let a: Loose<10> = 1000.into();
    let b: Loose<10> = a.log::<Loose<10>, Loose<10>>(10.into()).unwrap();
    assert_eq!(b, 3.into());
}

#[test]
fn log_2() {
    let a: Loose<10> = 100_000_000_000_000_000_000_u128.into();
    let b: Loose<10> = a.log::<Loose<10>, Loose<10>>(10.into()).unwrap();
    assert_eq!(b, 20.into());
}

#[test]
fn log_3() {
    let a: Loose<10> = "1840304903118662555886854371754653402172820247670630063406265913840381".parse().unwrap();
    let b: Loose<10> = a.log::<Loose<10>, Loose<10>>(4421.into()).unwrap();
    assert_eq!(b, 19.into());
}

#[test]
fn log_4() {
    let a: Loose<10> = "158456325028528675187087900672".parse().unwrap();
    let b: Loose<10> = a.log::<Loose<10>, Loose<10>>(2.into()).unwrap();
    assert_eq!(b, 97.into());
}

#[test]
fn fuzzy_log() {
    for (base, exp) in test_pairs!([u8; 100], [u16; 1000]) {
        let base: LooseBytes<10> = base.max(2).into();
        let exp: LooseBytes<10> = (exp % 32).max(0).into();
        let expd: LooseBytes<10> = base.clone().exp(exp.clone()).unwrap();
        assert_eq!(expd.clone().log::<LooseBytes<10>, LooseBytes<10>>(base.clone()).unwrap(), exp, "log({expd})_{base} = {exp}");
    }
}

// #[test]
// fn sqrt_1() {
//     let a: Loose<10> = 100.into();
//     assert_eq!(a.sqrt::<Loose<10>>().unwrap(), 10.into());
// }

// #[test]
// fn sqrt_2() {
//     let a: Loose<10> = 75069002792169_u128.into();
//     assert_eq!(a.sqrt::<Loose<10>>().unwrap(), 8664237.into());
// }

// #[test]
// fn sqrt_3() {
//     let a: Loose<10> = 16.into();
//     assert_eq!(a.sqrt::<Loose<10>>().unwrap(), 4.into());
// }

// #[test]
// fn fuzzy_sqrt() {
//     for (i, n) in test_values!([u8; 500], [u128; 1000]).enumerate() {
//         if i % 50 == 0 {
//             println!("{i}");
//         }
//         let n: Loose<10> = n.max(1).into();
//         let squared: Loose<10> = n.clone().exp(Loose::<10>::from(2)).unwrap();
//         assert_eq!(squared.clone().sqrt::<Loose<10>>().unwrap(), n, "sqrt({squared}) = {n}");
//     }
// }

#[test]
fn fuzzy_sqrt_2() {
    for (_i, n) in test_values!([u8; 500], [u128; 1000]).enumerate() {
        // if _i % 50 == 0 {
        //     println!("{i}");
        // }
        let n: Loose<10> = n.max(1).into();
        let squared: Loose<10> = n.clone().exp(Loose::<10>::from(2)).unwrap();
        assert_eq!(squared.clone().root::<Loose<10>, Loose<10>>(2.into()).unwrap(), n, "sqrt({squared}) = {n}");
    }
}

// #[test]
// fn fuzzy_cbrt() {
//     for (i, n) in test_values!([u8; 500], [u128; 1000]).enumerate() {
//         if i % 50 == 0 {
//             println!("{i}");
//         }
//         let n: Loose<10> = n.max(1).into();
//         let cubed: Loose<10> = n.clone().exp(Loose::<10>::from(3)).unwrap();
//         assert_eq!(cubed.clone().cbrt::<Loose<10>>().unwrap(), n, "cbrt({cubed}) = {n}");
//     }
// }

#[test]
fn fuzzy_cbrt_2() {
    for (_i, n) in test_values!([u8; 500], [u128; 1000]).enumerate() {
        // if _i % 50 == 0 {
        //     println!("{i}");
        // }
        let n: Loose<10> = n.max(1).into();
        let cubed: Loose<10> = n.clone().exp(Loose::<10>::from(3)).unwrap();
        assert_eq!(cubed.clone().root::<Loose<10>, Loose<10>>(3.into()).unwrap(), n, "cbrt({cubed}) = {n}");
    }
}

#[test]
fn root_1() {
    let a: Loose<10> = 27.into();
    assert_eq!(a.root::<Loose<10>, Loose<10>>(3.into()).unwrap(), 3.into());
}

#[test]
fn root_2() {
    let a: Loose<10> = 56311189175114996967_u128.into();
    assert_eq!(a.root::<Loose<10>, Loose<10>>(7.into()).unwrap(), 663.into());
}

#[test]
fn fuzzy_root() {
    for (base, exp) in test_pairs!([u8; 500], [u16; 2000]) {
        let base: Loose<10> = base.into();
        let exp: Loose<10> = (exp % 32).max(2).into();
        let expd: Loose<10> = base.clone().exp(exp.clone()).unwrap();
        assert_eq!(expd.clone().root::<_, Loose<10>>(exp.clone()).unwrap(), base, "root({expd})_{exp} = {base}");
    }
}
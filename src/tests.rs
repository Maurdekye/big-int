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
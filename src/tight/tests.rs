#[cfg(test)]
use super::*;

#[test]
fn push_binary_digits() {
    let mut builder = TightBuilder::<2>::new();
    builder.push_back(1);
    builder.push_back(1);
    builder.push_back(0);
    builder.push_back(1);
    builder.push_back(0);
    builder.push_back(0);
    builder.push_back(1);
    assert_eq!(builder.0.data, VecDeque::from([0b11010010]));
}

#[test]
fn push_small_digits() {
    let mut builder = TightBuilder::<4>::new();
    builder.push_back(0b11);
    builder.push_back(0b00);
    builder.push_back(0b11);
    builder.push_back(0b00);
    assert_eq!(builder.0.data, VecDeque::from([0b11001100]));
}

#[test]
fn push_medium_digits() {
    let mut builder = TightBuilder::<8192>::new();
    builder.push_back(0b1010101010101);
    builder.push_back(0b1111111111111);
    assert_eq!(
        builder.0.data,
        VecDeque::from([0b10101010, 0b10101111, 0b11111111, 0b11000000])
    );
}

#[test]
fn push_large_digits() {
    let mut builder = TightBuilder::<1048576>::new();
    builder.push_back(0b11111111111111111111);
    builder.push_back(0b10010010010010010010);
    builder.push_back(0b01101101101101101101);
    assert_eq!(
        builder.0.data,
        VecDeque::from([
            0b11111111, 0b11111111, 0b11111001, 0b00100100, 0b10010010, 0b01101101, 0b10110110,
            0b11010000
        ])
    );
}

#[test]
fn push_front_binary_digits() {
    let mut builder = TightBuilder::<2>::new();
    builder.push_front(1);
    builder.push_front(1);
    builder.push_front(0);
    builder.push_front(1);
    builder.push_front(0);
    builder.push_front(0);
    builder.push_front(1);
    assert_eq!(builder.0.data, VecDeque::from([0b01001011]));
}

#[test]
fn push_front_small_digits() {
    let mut builder = TightBuilder::<4>::new();
    builder.push_front(0b11);
    builder.push_front(0b00);
    builder.push_front(0b11);
    builder.push_front(0b00);
    assert_eq!(builder.0.data, VecDeque::from([0b00110011]));
}

#[test]
fn push_front_medium_digits() {
    let mut builder = TightBuilder::<8192>::new();
    builder.push_front(0b1111111111111);
    builder.push_front(0b1010101010101);
    assert_eq!(
        builder.0.data,
        VecDeque::from([0b00000010, 0b10101010, 0b10111111, 0b11111111])
    );
}

#[test]
fn push_front_large_digits() {
    let mut builder = TightBuilder::<1048576>::new();
    builder.push_front(0b11111111111111111111);
    builder.push_front(0b10010010010010010010);
    builder.push_front(0b01101101101101101101);
    assert_eq!(
        builder.0.data,
        VecDeque::from([
            0b00000110, 0b11011011, 0b01101101, 0b10010010, 0b01001001, 0b00101111, 0b11111111,
            0b11111111
        ])
    );
}

#[test]
fn build() {
    let mut builder = TightBuilder::<8192>::new();
    builder.push_front(0b1111111111111);
    builder.push_front(0b1010101010101);
    let number: Tight<8192> = builder.into();
    assert_eq!(
        number.data,
        vec![0b10101010, 0b10101111, 0b11111111, 0b11000000]
    );
}

#[test]
fn build_2() {
    let builder = TightBuilder::<10>::new();
    let number: Tight<10> = builder.into();
    assert_eq!(number.data, vec![0]);
}

#[test]
fn build_3() {
    let mut builder = TightBuilder::<10>::new();
    builder.push_back(1);
    builder.push_back(2);
    builder.push_back(5);
    let int: Tight<10> = builder.into();
    assert_eq!(
        int,
        Tight::<10> {
            sign: Positive,
            data: VecDeque::from(vec![18, 80]),
            start_offset: 0,
            end_offset: 12,
        }
    );
}

#[test]
fn get_digit() {
    let mut builder = TightBuilder::<10>::new();
    builder.push_front(4);
    builder.push_front(3);
    builder.push_front(2);
    builder.push_front(1);
    let int: Tight<10> = builder.into();
    assert_eq!(int.get_digit(0), Some(1));
    assert_eq!(int.get_digit(1), Some(2));
    assert_eq!(int.get_digit(2), Some(3));
    assert_eq!(int.get_digit(3), Some(4));
    assert_eq!(int.get_digit(4), None);
}

#[test]
fn set_digit() {
    let mut builder = TightBuilder::<10>::new();
    builder.push_back(1);
    builder.push_back(2);
    builder.push_back(3);
    builder.push_back(4);
    let mut int: Tight<10> = builder.into();
    int.set_digit(1, 8);
    int.set_digit(2, 0);
    assert_eq!(int.get_digit(0), Some(1));
    assert_eq!(int.get_digit(1), Some(8));
    assert_eq!(int.get_digit(2), Some(0));
    assert_eq!(int.get_digit(3), Some(4));
    assert_eq!(int.get_digit(4), None);
}

#[test]
fn pop_back() {
    let mut a: Tight<10> = 651.into();
    let digit = unsafe { a.pop_back() };
    assert_eq!(a, 65.into());
    assert_eq!(digit, Some(1));
}

#[test]
fn as_iter() {
    let a: Tight<10> = 134522.into();
    let mut v = Vec::new();
    for digit in a {
        v.push(digit);
    }
    assert_eq!(v, vec![1, 3, 4, 5, 2, 2]);
}

#[test]
fn as_rev_iter() {
    let mut a: Tight<10> = 134522.into();
    let mut v = Vec::new();
    while let Some(digit) = a.next_back() {
        v.push(digit);
    }
    assert_eq!(v, vec![2, 2, 5, 4, 3, 1]);
}

// macro_rules! base_conv_print {
//     ($d:expr; $($b:literal),*) => {
//         let a: Tight<256> = $d.into();
//         printbytes!(a.data);
//         $(
//             let a: Tight<$b> = a.convert();
//             println!("{}: ", $b);
//             printbytes!(a.data);
//         )*
//     };
// }

// #[test]
// fn conversion_3() {
//     base_conv_print!([255, 0, 0, 0]; 128, 64, 32, 16, 8, 4, 2);
// }

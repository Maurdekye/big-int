use big_int::base64::{encode, decode};



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

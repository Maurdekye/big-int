//! base64 encoding & decoding, baked into the library :)

use crate::prelude::*;
/// Base64 alphabet; used for encoding & decoding numbers to and from base64.
pub const BASE64_ALPHABET: &str =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/// Encode an array of bytes into base64 data.
///
/// Note: probably slower than using a standalone
/// library to perform this conversion. However, it's very neat :3
///
/// ```
/// use big_int::base64::*;
///
/// assert_eq!(encode(b"Hello world!"), "SGVsbG8gd29ybGQh");
/// ```
pub fn encode(bytes: &[u8]) -> String {
    let mut digits = vec![255, 255, 255]
        .into_iter()
        .chain(bytes.into_iter().copied().map(Digit::from))
        .collect::<Vec<_>>();
    let padding = 3 - ((digits.len() - 1) % 3) - 1;
    digits.extend(vec![0; padding]);
    let data_as_int: Loose<256> = digits.iter().copied().collect();
    let base64_data: Loose<64> = data_as_int.convert();
    let base64_string = base64_data.display(BASE64_ALPHABET).unwrap();
    base64_string[4..base64_string.len() - padding].to_string()
}

/// Decode a base64 string into an array of bytes.
///
/// Note: probably slower than using a standalone
/// library to perform this conversion. However, again, it's very neat c:
///
/// ```
/// use big_int::base64::*;
///
/// assert_eq!(decode("SGVsbG8gd29ybGQh").unwrap(), b"Hello world!");
/// ```
pub fn decode(b64_string: impl Into<String>) -> Result<Vec<u8>, BigIntError> {
    let mut b64_string = b64_string.into();
    b64_string = format!("////{b64_string}");
    let padding = 4 - ((b64_string.len() - 1) % 4) - 1;
    b64_string.extend(vec!['A'; padding]);
    let string_as_int: Loose<64> =
        BigInt::parse(&b64_string, BASE64_ALPHABET).map_err(BigIntError::ParseFailed)?;
    let bytes_int: Loose<256> = string_as_int.convert();
    let bytes = bytes_int
        .iter()
        .map(u8::try_from)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let bytes = bytes[3..bytes.len() - padding].to_vec();
    Ok(bytes)
}

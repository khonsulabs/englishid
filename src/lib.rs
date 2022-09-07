#![doc = include_str!("../.rustme/docs.md")]
#![forbid(unsafe_code)]
#![warn(
    clippy::cargo,
    missing_docs,
    // clippy::missing_docs_in_private_items,
    clippy::nursery,
    clippy::pedantic,
    future_incompatible,
    rust_2018_idioms,
)]
#![allow(clippy::option_if_let_else, clippy::module_name_repetitions)]

mod wordlist;
use std::{
    collections::BTreeMap,
    fmt::{Display, Write},
};

use once_cell::sync::Lazy;
pub use wordlist::WORD_LIST;

static WORDLIST_LOOKUP: Lazy<BTreeMap<&'static str, usize>> = Lazy::new(|| {
    let mut words = BTreeMap::new();
    for (index, &word) in WORD_LIST.iter().enumerate() {
        words.insert(word, index);
    }
    words
});

/// An ID that can be converted to a set of "safe" words.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct EnglishId {
    /// The number of words to use for this id.
    words: usize,
    /// The value of the id.
    value: Unsigned,
}

impl EnglishId {
    /// Sets the number of words that will be used to encode this id.
    #[must_use]
    pub const fn words(mut self, words: usize) -> Self {
        self.words = words;
        self
    }

    /// Encode the id to a string.
    ///
    /// # Errors
    ///
    /// - [`Error::ValueOutOfRange`]: Returned if the value being encoded cannot
    ///   be expressed in the number of words specified.
    pub fn to_string(mut self) -> Result<String, Error> {
        let mut output = String::new();
        for word in &mut self {
            if !output.is_empty() {
                output.push('-');
            }
            output.push_str(word);
        }

        if self.value.is_zero() {
            Ok(output)
        } else {
            Err(Error::ValueOutOfRange)
        }
    }
}

#[allow(clippy::copy_iterator)]
impl Iterator for EnglishId {
    type Item = &'static str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.words > 0 {
            self.words -= 1;
            let word_index = self.value.modulo(WORD_LIST.len());
            self.value /= WORD_LIST.len();
            Some(WORD_LIST[word_index])
        } else {
            None
        }
    }
}

impl Display for EnglishId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut id = *self;
        for idx in 0..id.words {
            if idx > 0 {
                f.write_char('-')?;
            }
            let word_index = id.value.modulo(WORD_LIST.len());
            id.value /= WORD_LIST.len();
            f.write_str(WORD_LIST[word_index])?;
        }

        Ok(())
    }
}

/// An error from encoding or parsing an [`EnglishId`].
#[derive(thiserror::Error, Debug)]
pub enum Error {
    /// An empty string was provided as input.
    #[error("input was empty")]
    EmptyInput,
    /// A value was out of range. If encoding, the numerical value could not be
    /// expressed with the provided number of words. If parsing, the numerical
    /// value parsed is larger than the type being parsed into.
    #[error("value out of range")]
    ValueOutOfRange,
    /// A word not inside of the word list was encountered.
    #[error("an unknown word '{0}' was encountered")]
    UnknownWord(String),
    /// The data was too long to be encoded. The maximum number of bytes
    /// currently able to be encoded is 7,775.
    #[error("data too long")]
    DataTooLong,
}

#[derive(Eq, PartialEq, Debug, Copy, Clone)]
enum EncodeHeader {
    None,
    Length,
    Value(u16),
}

/// Encodes `data` using `englishid` with enough information to be able to be
/// decoded without additional information. To decode, use the [`decode()`]
/// function.
///
/// # Errors
///
/// - [`Error::DataTooLong`]: Returned if `data` is longer than 8,190 bytes.
pub fn encode(data: &[u8]) -> Result<String, Error> {
    internal_encode(data, EncodeHeader::Length)
}

/// Encodes `data` using `englishid`, for situations where the decoder knows the
/// expected length of `data`. To decode, use the [`decode_fixed_length()`]
/// function.
#[allow(clippy::missing_panics_doc)] // The only error that internal_encode returns can't be triggered from this flow
#[must_use]
pub fn encode_fixed_length(data: &[u8]) -> String {
    internal_encode(data, EncodeHeader::None).unwrap()
}

/// Encodes `data` using `englishid`, encoding `header` at the start. To decode, use the [`decode_with_custom_header()`]
/// function.
///
/// # Errors
///
/// - [`Error::DataTooLong`]: Returned if `data` is longer than 8,190 bytes.
pub fn encode_with_custom_header(data: &[u8], header: u16) -> Result<String, Error> {
    internal_encode(data, EncodeHeader::Value(header))
}

fn internal_encode(mut data: &[u8], header: EncodeHeader) -> Result<String, Error> {
    let mut words = Vec::new();
    let header_value = match header {
        EncodeHeader::None => None,
        EncodeHeader::Length => Some(data.len()),
        EncodeHeader::Value(value) => Some(value as usize),
    };

    if let Some(header_value) = header_value {
        if header_value >= WORD_LIST.len() - 1 {
            // We're reserving the last word to act as a sentinel value to allow
            // encoding multiple values. I can't imagine this library being used to
            // encode values larger than 32 or 64 bytes, so I would be shocked if we
            // ever expanded the ability here.
            return Err(Error::DataTooLong);
        }

        words.push(WORD_LIST[header_value]);
    }

    let max_word = 2_u32.pow(13);

    let mut accumulated_value = 0_u32;
    let mut accumulated_bits = 0_usize;
    while !data.is_empty() || accumulated_bits > 0 {
        // Load bytes into accumulated_value if we can't perform our division
        // and modulus safely.
        while !data.is_empty() && accumulated_bits < 13 {
            accumulated_value <<= 8;
            accumulated_value |= u32::from(data[0]);
            accumulated_bits += 8;
            data = &data[1..];
        }
        let leftover_bits = accumulated_bits.saturating_sub(13);
        let mut word_index = accumulated_value >> leftover_bits & (max_word - 1);

        accumulated_value = if leftover_bits > 0 {
            accumulated_value & (u32::MAX >> (32 - leftover_bits))
        } else {
            0
        };
        if data.is_empty() && leftover_bits == 0 {
            word_index <<= 13 - accumulated_bits;
        }
        words.push(WORD_LIST[word_index as usize]);
        accumulated_bits = leftover_bits;
    }
    Ok(words.join("-"))
}

enum DecodeMode {
    FixedLength(usize),
    LengthHeader,
    ValueHeader(Box<dyn FnOnce(u16) -> usize>),
}

/// Decodes `englishid` that was previously encoded using
/// [`encode_fixed_length()`]., expecting an output size of `length`.
///
/// # Errors
///
/// - `Error::EmptyInput`: `englishid` was empty.
/// - `Error::UnknownWord`: An unrecognized word was encountered.
pub fn decode_fixed_length(englishid: &str, length: usize) -> Result<Vec<u8>, Error> {
    internal_decode(englishid, DecodeMode::FixedLength(length))
}

/// Decodes `englishid` that was previously encoded using [`encode()`].
///
/// # Errors
///
/// - `Error::EmptyInput`: `englishid` was empty.
/// - `Error::UnknownWord`: An unrecognized word was encountered.
pub fn decode(englishid: &str) -> Result<Vec<u8>, Error> {
    internal_decode(englishid, DecodeMode::LengthHeader)
}

/// Decodes `englishid` that was previously encoded using
/// [`encode_with_custom_header()`]. After parsing the embedded header,
/// `callback` is invoked with the value. The callback is responsible for
/// returning the number of bytes the result is expected to contain.
///
/// # Errors
///
/// - `Error::EmptyInput`: `englishid` was empty.
/// - `Error::UnknownWord`: An unrecognized word was encountered.
pub fn decode_with_custom_header<F: FnOnce(u16) -> usize + 'static>(
    englishid: &str,
    callback: F,
) -> Result<Vec<u8>, Error> {
    internal_decode(englishid, DecodeMode::ValueHeader(Box::new(callback)))
}

#[allow(clippy::cast_possible_truncation)]
fn internal_decode(englishid: &str, header: DecodeMode) -> Result<Vec<u8>, Error> {
    let mut words = englishid.split('-');
    let length = match header {
        DecodeMode::FixedLength(length) => length,
        DecodeMode::LengthHeader => {
            let length_word = words.next().ok_or(Error::EmptyInput)?;
            *WORDLIST_LOOKUP
                .get(length_word)
                .ok_or_else(|| Error::UnknownWord(length_word.to_string()))?
        }
        DecodeMode::ValueHeader(callback) => {
            let value_word = words.next().ok_or(Error::EmptyInput)?;
            let value = *WORDLIST_LOOKUP
                .get(value_word)
                .ok_or_else(|| Error::UnknownWord(value_word.to_string()))?;
            callback(value as u16)
        }
    };

    let mut output = Vec::with_capacity(length);

    let mut accumulated_value = 0_u32;
    let mut accumulated_bits = 0_usize;

    for word in words {
        accumulated_value <<= 13;
        accumulated_value |= *WORDLIST_LOOKUP
            .get(word)
            .ok_or_else(|| Error::UnknownWord(word.to_string()))?
            as u32;
        accumulated_bits += 13;

        while accumulated_bits > 8 {
            let leftover_bits = accumulated_bits.saturating_sub(8);
            output.push((accumulated_value >> leftover_bits) as u8);
            accumulated_value = if leftover_bits > 0 {
                accumulated_value & (u32::MAX >> (32 - leftover_bits))
            } else {
                0
            };
            accumulated_bits = leftover_bits;
        }
    }

    if accumulated_bits > 0 {
        output.push((accumulated_value << (13 - accumulated_bits)) as u8);
    }

    output.resize(length, 0);

    Ok(output)
}

#[test]
fn encode_test() {
    const BUFFER: &[u8; 13] = b"Hello, world!";

    for length in 1..BUFFER.len() {
        let test_slice = &BUFFER[0..length];
        let encoded = encode_fixed_length(test_slice);
        let decoded = decode_fixed_length(&encoded, length).unwrap();
        assert_eq!(decoded, test_slice);
    }
}

#[test]
fn encode_with_length_test() {
    const BUFFER: &[u8; 13] = b"Hello, world!";

    for length in 1..BUFFER.len() {
        let test_slice = &BUFFER[0..length];
        let encoded = encode(test_slice).unwrap();
        let decoded = decode(&encoded).unwrap();
        assert_eq!(decoded, test_slice);
    }
}

#[test]
#[allow(clippy::cast_possible_truncation)]
fn encode_with_custom_header_test() {
    const BUFFER: &[u8; 13] = b"Hello, world!";

    for length in 1..BUFFER.len() {
        let test_slice = &BUFFER[0..length];
        let encoded = encode_with_custom_header(test_slice, (length as u16) << 1).unwrap();
        let decoded = decode_with_custom_header(&encoded, |header| header as usize >> 1).unwrap();
        assert_eq!(decoded, test_slice);
    }
}

/// Parses a previously-encoded [`EnglishId`].
///
/// # Errors
///
/// - [`Error::UnknownWord`]: A word could not be found in the word list.
/// - [`Error::ValueOutOfRange`]: The parsed value could not fit in the output type.
pub fn parse_u8(englishid: &str) -> Result<u8, Error> {
    // For a u8, it can only be a single word
    if let Some(word) = WORDLIST_LOOKUP.get(englishid) {
        u8::try_from(*word).map_err(|_| Error::ValueOutOfRange)
    } else {
        Err(Error::UnknownWord(englishid.to_owned()))
    }
}

macro_rules! impl_parse {
    ($name:ident, $primitive:ident) => {
        /// Parses a previously-encoded [`EnglishId`].
        ///
        /// # Errors
        ///
        /// - [`Error::UnknownWord`]: A word could not be found in the word list.
        /// - [`Error::ValueOutOfRange`]: The parsed value could not fit in the output type.
        pub fn $name(englishid: &str) -> Result<$primitive, Error> {
            let mut value: $primitive = 0;
            let words = englishid.split('-').collect::<Vec<_>>();
            for (index, word) in words.into_iter().rev().enumerate() {
                if index > 0 {
                    if let Some(new_value) = value.checked_mul(WORD_LIST.len() as $primitive) {
                        value = new_value;
                    } else {
                        return Err(Error::ValueOutOfRange);
                    }
                }
                let word_index = WORDLIST_LOOKUP
                    .get(word)
                    .ok_or_else(|| Error::UnknownWord(word.to_string()))?;
                if let Some(new_value) = value.checked_add(*word_index as $primitive) {
                    value = new_value;
                } else {
                    return Err(Error::ValueOutOfRange);
                }
            }
            Ok(value)
        }
    };
}

impl_parse!(parse_u16, u16);
impl_parse!(parse_u32, u32);
impl_parse!(parse_u64, u64);
impl_parse!(parse_u128, u128);

/// An unsigned integer value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum Unsigned {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
}

impl Unsigned {
    /// Calculates the modulus of self and `other`.
    #[allow(clippy::cast_possible_truncation)]
    #[must_use]
    pub const fn modulo(self, other: usize) -> usize {
        match self {
            Self::U8(value) => value as usize % other,
            Self::U16(value) => value as usize % other,
            Self::U32(value) => value as usize % other,
            Self::U64(value) => (value % other as u64) as usize,
            Self::U128(value) => (value % other as u128) as usize,
        }
    }

    /// Returns true if the value is 0.
    #[must_use]
    pub const fn is_zero(self) -> bool {
        match self {
            Self::U8(value) => value == 0,
            Self::U16(value) => value == 0,
            Self::U32(value) => value == 0,
            Self::U64(value) => value == 0,
            Self::U128(value) => value == 0,
        }
    }
}

impl std::ops::DivAssign<usize> for Unsigned {
    fn div_assign(&mut self, rhs: usize) {
        match self {
            Self::U8(value) => *value /= u8::try_from(rhs).unwrap_or(u8::MAX),
            Self::U16(value) => *value /= u16::try_from(rhs).unwrap_or(u16::MAX),
            Self::U32(value) => *value /= u32::try_from(rhs).unwrap_or(u32::MAX),
            Self::U64(value) => *value /= u64::try_from(rhs).unwrap_or(u64::MAX),
            Self::U128(value) => *value /= u128::try_from(rhs).unwrap_or(u128::MAX),
        }
    }
}

macro_rules! impl_from_primitive_for_unsigned {
    ($primitive:ident, $name:ident) => {
        impl From<$primitive> for Unsigned {
            fn from(value: $primitive) -> Self {
                Self::$name(value)
            }
        }
    };
}

impl_from_primitive_for_unsigned!(u8, U8);
impl_from_primitive_for_unsigned!(u16, U16);
impl_from_primitive_for_unsigned!(u32, U32);
impl_from_primitive_for_unsigned!(u64, U64);
impl_from_primitive_for_unsigned!(u128, U128);

impl From<u8> for EnglishId {
    fn from(value: u8) -> Self {
        Self {
            words: 1,
            value: Unsigned::from(value),
        }
    }
}

impl From<u16> for EnglishId {
    fn from(value: u16) -> Self {
        Self {
            words: 2,
            value: Unsigned::from(value),
        }
    }
}

impl From<u32> for EnglishId {
    fn from(value: u32) -> Self {
        Self {
            words: 3,
            value: Unsigned::from(value),
        }
    }
}

impl From<u64> for EnglishId {
    fn from(value: u64) -> Self {
        Self {
            words: 5,
            value: Unsigned::from(value),
        }
    }
}

impl From<u128> for EnglishId {
    fn from(value: u128) -> Self {
        Self {
            words: 10,
            value: Unsigned::from(value),
        }
    }
}

#[test]
fn numeric_roundtrip_tests() {
    assert_eq!(
        parse_u8(&EnglishId::from(0_u8).to_string().unwrap()).unwrap(),
        0
    );
    assert_eq!(
        parse_u8(&EnglishId::from(1_u8).to_string().unwrap()).unwrap(),
        1
    );
    assert_eq!(
        parse_u16(&EnglishId::from(1_u16).to_string().unwrap()).unwrap(),
        1
    );
    assert_eq!(
        parse_u16(&EnglishId::from(7777_u16).to_string().unwrap()).unwrap(),
        7777
    );
    assert_eq!(
        parse_u16(&EnglishId::from(u16::MAX).to_string().unwrap()).unwrap(),
        u16::MAX
    );
    assert_eq!(
        parse_u32(&EnglishId::from(u32::MAX).to_string().unwrap()).unwrap(),
        u32::MAX
    );
    assert_eq!(
        parse_u64(&EnglishId::from(u64::MAX).to_string().unwrap()).unwrap(),
        u64::MAX
    );
    assert_eq!(
        parse_u128(&EnglishId::from(u128::MAX).to_string().unwrap()).unwrap(),
        u128::MAX
    );
}

#[test]
fn numeric_out_of_range_tests() {
    assert!(matches!(
        parse_u8(WORD_LIST[256]),
        Err(Error::ValueOutOfRange)
    ));
    assert!(matches!(
        parse_u16(
            &EnglishId::from(u32::from(u16::MAX) + 1)
                .to_string()
                .unwrap()
        ),
        Err(Error::ValueOutOfRange)
    ));
    assert!(matches!(
        parse_u32(
            &EnglishId::from(u64::from(u32::MAX) + 1)
                .to_string()
                .unwrap()
        ),
        Err(Error::ValueOutOfRange)
    ));
    assert!(matches!(
        parse_u64(
            &EnglishId::from(u128::from(u64::MAX) + 1)
                .to_string()
                .unwrap()
        ),
        Err(Error::ValueOutOfRange)
    ));
    assert!(matches!(
        parse_u128("zoom-zoom-zoom-zoom-zoom-zoom-zoom-zoom-zoom-zoom"),
        Err(Error::ValueOutOfRange)
    ));
}

#[test]
fn numeric_restricted_words_test() {
    // Test storing 26 bits of data in 2 words
    assert_eq!(
        parse_u32(
            &EnglishId::from(2_u32.pow(26) - 1)
                .words(2)
                .to_string()
                .unwrap()
        )
        .unwrap(),
        0x3ff_ffff
    );

    assert!(matches!(
        EnglishId::from(2_u32.pow(26)).words(2).to_string(),
        Err(Error::ValueOutOfRange)
    ));

    // Test storing 52 bits of data in 4 words
    assert_eq!(
        parse_u64(
            &EnglishId::from(2_u64.pow(52) - 1)
                .words(4)
                .to_string()
                .unwrap()
        )
        .unwrap(),
        0xf_ffff_ffff_ffff
    );

    assert!(matches!(
        EnglishId::from(2_u64.pow(52)).words(4).to_string(),
        Err(Error::ValueOutOfRange)
    ));
}

#[test]
fn validate_wordlist() {
    for word in &crate::wordlist::WORD_LIST {
        dbg!(word);
        // Should be all lower-case
        assert_eq!(word, &word.to_lowercase());
        // Hyphens in words breaks splitting during parsing
        assert!(!word.contains('-'));
        // Words shouldn't contain spaces
        assert!(!word.contains(' '));
        // Should be no duplicates
        assert_eq!(
            crate::wordlist::WORD_LIST
                .iter()
                .filter(|x| x == &word)
                .count(),
            1
        );
    }
}

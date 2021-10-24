//! English formatting for unsigned integers. Useful for encoding large IDs in a
//! human-readable and recognizable format.
//!
//! ## Basic Usage
//!
//! Generating an ID can be done from any primitive unsigned integer type:
//!
//! ```rust
//! use englishid::EnglishId;
//!
//! let english_id = EnglishId::from(42_u16).to_string().unwrap();
//! assert_eq!(english_id, "acting-abacus");
//! ```
//!
//! Use the corresponding parse method to extract the encoded id:
//!
//! ```rust
//! let parsed = englishid::parse_u16("acting-abacus").unwrap();
//! assert_eq!(parsed, 42);
//! ```
//!
//! ## Restricting word-length
//!
//! The [wordlist](EFF_WORD_LIST) used can encode 51 bits of information in 4
//! words. If you'd prefer to restrict your u64 IDs to 51 bits, you can set the
//! number of words used:
//!
//! ```rust
//! use englishid::{EnglishId};
//!
//! let english_id = EnglishId::from(123456789_u64).words(4).to_string().unwrap();
//! assert_eq!(english_id, "quantum-ashamed-abdominal-abacus");
//! ```
//!
//! If a value is ever out of acceptable ranges, [`Error::ValueOutOfRange`] will
//! be returned.

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
pub use wordlist::EFF_WORD_LIST;

static WORDLIST_LOOKUP: Lazy<BTreeMap<&'static str, usize>> = Lazy::new(|| {
    let mut words = BTreeMap::new();
    for (index, word) in EFF_WORD_LIST.into_iter().enumerate() {
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
            let word_index = self.value.modulo(EFF_WORD_LIST.len());
            self.value /= EFF_WORD_LIST.len();
            Some(EFF_WORD_LIST[word_index])
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
            let word_index = id.value.modulo(EFF_WORD_LIST.len());
            id.value /= EFF_WORD_LIST.len();
            f.write_str(EFF_WORD_LIST[word_index])?;
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
    #[error("an unknown word was encountered")]
    UnknownWord(String),
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
                    if let Some(new_value) = value.checked_mul(EFF_WORD_LIST.len() as $primitive) {
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
            Unsigned::U8(value) => value as usize % other,
            Unsigned::U16(value) => value as usize % other,
            Unsigned::U32(value) => value as usize % other,
            Unsigned::U64(value) => (value % other as u64) as usize,
            Unsigned::U128(value) => (value % other as u128) as usize,
        }
    }

    /// Returns true if the value is 0.
    #[must_use]
    pub const fn is_zero(self) -> bool {
        match self {
            Unsigned::U8(value) => value == 0,
            Unsigned::U16(value) => value == 0,
            Unsigned::U32(value) => value == 0,
            Unsigned::U64(value) => value == 0,
            Unsigned::U128(value) => value == 0,
        }
    }
}

impl std::ops::DivAssign<usize> for Unsigned {
    fn div_assign(&mut self, rhs: usize) {
        match self {
            Unsigned::U8(value) => *value /= u8::try_from(rhs).unwrap_or(u8::MAX),
            Unsigned::U16(value) => *value /= u16::try_from(rhs).unwrap_or(u16::MAX),
            Unsigned::U32(value) => *value /= u32::try_from(rhs).unwrap_or(u32::MAX),
            Unsigned::U64(value) => *value /= u64::try_from(rhs).unwrap_or(u64::MAX),
            Unsigned::U128(value) => *value /= u128::try_from(rhs).unwrap_or(u128::MAX),
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
fn tests() {
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
    assert!(matches!(
        parse_u8(EFF_WORD_LIST[256]),
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

    assert!(matches!(
        EnglishId::from(2_u64.pow(52)).words(4).to_string(),
        Err(Error::ValueOutOfRange)
    ));
}

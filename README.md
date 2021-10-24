# englishid

![englishid forbids unsafe code](https://img.shields.io/badge/unsafe-forbid-success)
[![crate version](https://img.shields.io/crates/v/englishid.svg)](https://crates.io/crates/englishid)
[![Live Build Status](https://img.shields.io/github/workflow/status/khonsulabs/englishid/Tests/main)](https://github.com/khonsulabs/englishid/actions?query=workflow:Tests)
[![Documentation for `main` branch](https://img.shields.io/badge/docs-main-informational)](https://englishid.dev/main/englishid/)

English formatting for unsigned integers. Useful for encoding large IDs in a
human-readable and recognizable format.

## Basic Usage

Generating an ID can be done from any primitive unsigned integer type:

```rust
use englishid::EnglishId;

let english_id = EnglishId::from(42_u16).to_string().unwrap();
assert_eq!(english_id, "acting-abacus");
```

Use the corresponding parse method to extract the encoded id:

```rust
let parsed = englishid::parse_u16("acting-abacus").unwrap();
assert_eq!(parsed, 42);
```

## Restricting word-length

The [wordlist](EFF_WORD_LIST) used can encode 51 bits of information in 4
words. If you'd prefer to restrict your u64 IDs to 51 bits, you can set the
number of words used:

```rust
use englishid::{EnglishId};

let english_id = EnglishId::from(123456789_u64).words(4).to_string().unwrap();
assert_eq!(english_id, "quantum-ashamed-abdominal-abacus");
```

If a value is ever out of acceptable ranges, [`Error::ValueOutOfRange`] will
be returned.
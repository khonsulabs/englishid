English formatting for unsigned integer IDs and arbitrary data.

![englishid forbids unsafe code](https://img.shields.io/badge/unsafe-forbid-success)
[![crate version](https://img.shields.io/crates/v/englishid.svg)](https://crates.io/crates/englishid)
[![Live Build Status](https://img.shields.io/github/workflow/status/khonsulabs/englishid/Tests/main)](https://github.com/khonsulabs/englishid/actions?query=workflow:Tests)
[![Documentation for `main` branch](https://img.shields.io/badge/docs-main-informational)](https://khonsulabs.github.io/englishid/main/englishid/)

English formatting for unsigned integers. Useful for encoding large IDs in a
human-readable and recognizable format. Uses a modified [list of words][wordlist] based on
a [list created by the EFF][effwordlist].

## Basic Usage

Generating an ID can be done from any primitive unsigned integer type:

```rust
use englishid::EnglishId;

let english_id = EnglishId::from(42_u16).to_string().unwrap();
assert_eq!(english_id, "accept-abacus");
```

Use the corresponding parse method to extract the encoded id:

```rust
let parsed = englishid::parse_u16("accept-abacus").unwrap();
assert_eq!(parsed, 42);
```

## Restricting word-length

The [wordlist][wordlist] used can encode 52 bits of information in 4 words. If
you'd prefer to restrict your u64 IDs to 52 bits, you can set the number of
words used:

```rust
use englishid::EnglishId;

let english_id = EnglishId::from(123456789_u64).words(4).to_string().unwrap();
assert_eq!(english_id, "haunt-subtitle-abandon-abacus");
assert_eq!(englishid::parse_u64(&english_id).unwrap(), 123456789_u64);
```

If a value is ever out of acceptable ranges, `Error::ValueOutOfRange` will be
returned.

## Encoding/decoding arbitrary data

This crate also offers functions that allow encoding arbitrary bytes of
information using the same word list. If you will always know the data size, you
can use the `fixed_length` functions:

```rust
let payload = b"hello world";
let encoded = englishid::encode_fixed_length(payload);
assert_eq!(encoded, "hatchback-reissue-residual-overbuilt-ladybug-tusk-buffing");
assert_eq!(englishid::decode_fixed_length(&encoded, payload.len()).unwrap(), payload);
```

If you are encoding payloads of differing lengths and want the length to be
encoded into the resulting `englishid` string, `encode()` and `decode()` will do
that for you:

```rust
let payload = b"hello world";
let encoded = englishid::encode(payload).unwrap();
assert_eq!(encoded, "able-hatchback-reissue-residual-overbuilt-ladybug-tusk-buffing");
assert_eq!(englishid::decode(&encoded).unwrap(), payload);
```

Or, if you have an enum that can correspond to a byte length, you can use a custom header value:

```rust
enum PrivateKey {
    Ed25519([u8; 32]),
    Ed448([u8; 56])
}

impl PrivateKey {
    fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Ed25519(key) => key,
            Self::Ed448(key) => key,
        }
    }

    fn kind(&self) -> u16 {
        match self {
            Self::Ed25519(_) => 1,
            Self::Ed448(_) => 2,
        }
    }

    fn byte_length(kind: u16) -> usize {
        match kind {
            1 => 32,
            2 => 56,
            _ => 0,
        }
    }
}

let key = PrivateKey::Ed25519([0; 32]);
let encoded = englishid::encode_with_custom_header(key.as_bytes(), key.kind()).unwrap();
assert_eq!(englishid::decode_with_custom_header(&encoded, PrivateKey::byte_length).unwrap(), key.as_bytes());
```

### Limits on data encoding

When encoding using the `fixed_length` APIs, there is no limit to the amount of
data that can be encoded.

When using the automatic length header or a custom header, the value in the
header cannot be larger than 8190. This limit may be removed in the future, but
this crate is not intended for large payload encoding.

## Version stability

The maintainers of this crate will treat changes to the wordlist as breaking
changes in the eyes of semantic versioning. In the future, this crate [may
support](https://github.com/khonsulabs/englishid/issues/2) additional wordlists
which will provide another mechanism to releasing wordlist updates, which should
be infrequent.

If an issue is discovered that generated data that was unable to be recovered
into its original form, fixes will be shipped on minor releases and versions
that can generate invalid data will be yanked.

[wordlist]: https://github.com/khonsulabs/englishid/blob/main/src/wordlist.rs
[effwordlist]: https://www.eff.org/deeplinks/2016/07/new-wordlists-random-passphrases

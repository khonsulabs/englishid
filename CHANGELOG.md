# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## v0.3

### Fixes / Breaking Changes

- Issues with the word list were addressed by @dbr in pull request
  [#1](https://github.com/khonsulabs/englishid/pull/1). The words "opt" and
  "try" were in the list twice and five words included the hyphen character.
  Both would generate englishid-encoded data successfully, but in almost all
  circumstances where those words were selected, parsing would fail.

## v0.2

### Breaking Changes

- The wordlist has been expanded to 8,192 entries.
- APIs that enable encoding arbitrary data have been added.

## v0.1

- Initial release.

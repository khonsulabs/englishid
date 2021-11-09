initSidebarItems({"enum":[["Error","An error from encoding or parsing an [`EnglishId`]."]],"fn":[["decode","Decodes `englishid` that was previously encoded using [`encode()`]."],["decode_fixed_length","Decodes `englishid` that was previously encoded using [`encode_fixed_length()`]., expecting an output size of `length`."],["decode_with_custom_header","Decodes `englishid` that was previously encoded using [`encode_with_custom_header()`]. After parsing the embedded header, `callback` is invoked with the value. The callback is responsible for returning the number of bytes the result is expected to contain."],["encode","Encodes `data` using `englishid` with enough information to be able to be decoded without additional information. To decode, use the [`decode()`] function."],["encode_fixed_length","Encodes `data` using `englishid`, for situations where the decoder knows the expected length of `data`. To decode, use the [`decode_fixed_length()`] function."],["encode_with_custom_header","Encodes `data` using `englishid`, encoding `header` at the start. To decode, use the [`decode_with_custom_header()`] function."],["parse_u128","Parses a previously-encoded [`EnglishId`]."],["parse_u16","Parses a previously-encoded [`EnglishId`]."],["parse_u32","Parses a previously-encoded [`EnglishId`]."],["parse_u64","Parses a previously-encoded [`EnglishId`]."],["parse_u8","Parses a previously-encoded [`EnglishId`]."]],"static":[["WORD_LIST","A list of words based on the list created by the EFF, but with some additional words to expand the list to 8,192 entries."]],"struct":[["EnglishId","An ID that can be converted to a set of “safe” words."]]});
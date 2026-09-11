//! Numeric-candidate scanning and validation.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum NumberClass {
    Integer,
    Float,
}

/// Scans one complete numeric candidate while preserving punctuation boundaries.
pub(super) fn scan(bytes: &[u8], start: usize) -> (usize, Option<NumberClass>) {
    let mut offset = start;

    if bytes[start..].starts_with(b"0x")
        || bytes[start..].starts_with(b"0o")
        || bytes[start..].starts_with(b"0b")
    {
        offset += 2;
        while bytes
            .get(offset)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        {
            offset += 1;
        }
    } else {
        let mut has_dot = false;
        let mut has_exponent = false;
        let mut suffix_started = false;
        let mut exponent_sign_allowed = false;

        while let Some(&byte) = bytes.get(offset) {
            if byte.is_ascii_digit() || byte == b'_' {
                exponent_sign_allowed = false;
                offset += 1;
            } else if byte.is_ascii_alphabetic() {
                if matches!(byte, b'e' | b'E') && !has_exponent && !suffix_started {
                    has_exponent = true;
                    exponent_sign_allowed = true;
                } else {
                    suffix_started = true;
                    exponent_sign_allowed = false;
                }
                offset += 1;
            } else if matches!(byte, b'+' | b'-') && exponent_sign_allowed {
                exponent_sign_allowed = false;
                offset += 1;
            } else if byte == b'.'
                && !has_dot
                && !has_exponent
                && !suffix_started
                && bytes.get(offset + 1).is_some_and(u8::is_ascii_digit)
            {
                has_dot = true;
                exponent_sign_allowed = false;
                offset += 1;
            } else {
                break;
            }
        }
    }

    (offset, classify(&bytes[start..offset]))
}

fn classify(raw: &[u8]) -> Option<NumberClass> {
    let text = std::str::from_utf8(raw).ok()?;
    if validate_integer(text) {
        Some(NumberClass::Integer)
    } else if validate_float(text) {
        Some(NumberClass::Float)
    } else {
        None
    }
}

fn validate_integer(text: &str) -> bool {
    const SUFFIXES: [&str; 12] = [
        "isize", "usize", "i16", "i32", "i64", "u16", "u32", "u64", "i8", "u8", "i128", "u128",
    ];
    let (body, suffix) = split_suffix(text, &SUFFIXES);
    if matches!(suffix, Some("i128" | "u128")) {
        return false;
    }
    let (digits, radix) = if let Some(rest) = body.strip_prefix("0x") {
        (rest, 16)
    } else if let Some(rest) = body.strip_prefix("0o") {
        (rest, 8)
    } else if let Some(rest) = body.strip_prefix("0b") {
        (rest, 2)
    } else {
        (body, 10)
    };
    if radix == 10 && digits.len() > 1 && digits.starts_with('0') {
        return false;
    }
    valid_digit_sequence(digits, radix)
}

fn validate_float(text: &str) -> bool {
    const SUFFIXES: [&str; 3] = ["f16", "f32", "f64"];
    let (body, suffix) = split_suffix(text, &SUFFIXES);
    let (mantissa, exponent) = match body.find(['e', 'E']) {
        Some(index) => (&body[..index], Some(&body[index + 1..])),
        None => (body, None),
    };
    if exponent.is_some_and(|value| {
        let digits = value.strip_prefix(['+', '-']).unwrap_or(value);
        !valid_digit_sequence(digits, 10)
    }) {
        return false;
    }
    let valid_mantissa = if let Some(dot) = mantissa.find('.') {
        valid_decimal_body(&mantissa[..dot])
            && valid_digit_sequence(&mantissa[dot + 1..], 10)
            && !mantissa[dot + 1..].is_empty()
    } else {
        valid_decimal_body(mantissa)
    };
    valid_mantissa && (mantissa.contains('.') || exponent.is_some() || suffix.is_some())
}

fn valid_decimal_body(text: &str) -> bool {
    valid_digit_sequence(text, 10) && (text == "0" || !text.starts_with('0'))
}

fn valid_digit_sequence(text: &str, radix: u32) -> bool {
    if text.is_empty() || text.starts_with('_') || text.ends_with('_') {
        return false;
    }
    let bytes = text.as_bytes();
    bytes.iter().enumerate().all(|(index, byte)| {
        if *byte == b'_' {
            index > 0
                && index + 1 < bytes.len()
                && (bytes[index - 1] as char).is_digit(radix)
                && (bytes[index + 1] as char).is_digit(radix)
        } else {
            (*byte as char).is_digit(radix)
        }
    })
}

fn split_suffix<'text>(text: &'text str, suffixes: &[&str]) -> (&'text str, Option<&'text str>) {
    for suffix in suffixes {
        if let Some(body) = text.strip_suffix(suffix) {
            return (body, Some(&text[body.len()..]));
        }
    }
    (text, None)
}

#[cfg(test)]
mod tests {
    use super::{NumberClass, scan};

    fn scan_text(text: &str) -> (&str, Option<NumberClass>) {
        let (end, class) = scan(text.as_bytes(), 0);
        (&text[..end], class)
    }

    #[test]
    fn operators_after_hex_digits_and_suffixes_remain_punctuation() {
        assert_eq!(scan_text("0xbe+1"), ("0xbe", Some(NumberClass::Integer)));
        assert_eq!(
            scan_text("1usize+2"),
            ("1usize", Some(NumberClass::Integer))
        );
        assert_eq!(scan_text("0xff.0"), ("0xff", Some(NumberClass::Integer)));
        assert_eq!(scan_text("1e2.3"), ("1e2", Some(NumberClass::Float)));
    }

    #[test]
    fn decimal_exponent_sign_and_fraction_remain_inside_float() {
        assert_eq!(scan_text("1.25e+2;"), ("1.25e+2", Some(NumberClass::Float)));
        assert_eq!(scan_text("1e-2+3"), ("1e-2", Some(NumberClass::Float)));
    }

    #[test]
    fn malformed_candidates_still_consume_identifier_continuations() {
        assert_eq!(scan_text("123abc+1"), ("123abc", None));
        assert_eq!(scan_text("0b102+1"), ("0b102", None));
    }
}

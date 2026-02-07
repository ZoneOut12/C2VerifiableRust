#[derive(PartialEq)]
enum Kind {
    LOWER,
    UPPER,
    DIGIT,
    OTHER,
}

use Kind::*;

fn is_lower_alpha(c: char) -> bool {
    'a' <= c && c <= 'z'
}

fn is_upper_alpha(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'
}

fn character_kind(c: char) -> Kind {
    if is_lower_alpha(c) {
        LOWER
    } else if is_upper_alpha(c) {
        UPPER
    } else if is_digit(c) {
        DIGIT
    } else {
        OTHER
    }
}
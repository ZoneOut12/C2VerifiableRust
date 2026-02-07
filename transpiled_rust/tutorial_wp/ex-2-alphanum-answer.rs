enum Kind {
    LOWER,
    UPPER,
    DIGIT,
    OTHER,
}

use Kind::*;

fn is_lower_alpha(c: char) -> i32 {
    (c >= 'a' && c <= 'z') as i32
}

fn is_upper_alpha(c: char) -> i32 {
    (c >= 'A' && c <= 'Z') as i32
}

fn is_digit(c: char) -> i32 {
    (c >= '0' && c <= '9') as i32
}

fn character_kind(c: char) -> Kind {
    if is_lower_alpha(c) != 0 {
        return LOWER;
    }
    if is_upper_alpha(c) != 0 {
        return UPPER;
    }
    if is_digit(c) != 0 {
        return DIGIT;
    }
    OTHER
}
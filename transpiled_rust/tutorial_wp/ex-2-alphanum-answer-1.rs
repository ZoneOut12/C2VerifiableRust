fn is_lower_alpha(c: char) -> i32 {
    ('a' <= c && c <= 'z') as i32
}

fn is_upper_alpha(c: char) -> i32 {
    ('A' <= c && c <= 'Z') as i32
}

fn is_digit(c: char) -> i32 {
    ('0' <= c && c <= '9') as i32
}

fn is_alpha_num(c: char) -> i32 {
    (is_lower_alpha(c) != 0 || is_upper_alpha(c) != 0 || is_digit(c) != 0) as i32
}
fn alphabet_letter(c: char) -> i32 {
    if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') {
        1
    } else {
        0
    }
}

fn main() {
    let mut r: i32;
    r = alphabet_letter('x');
    // verus_assert(1);
    r = alphabet_letter('H');
    // verus_assert(2);
    r = alphabet_letter(' ');
    // verus_assert(3);
}
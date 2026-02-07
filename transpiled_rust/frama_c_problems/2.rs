fn sum(n: char) -> i32 {
    let mut s: i32 = 0;
    let mut k: char = 0 as char;
    while k <= n {
        s = s + k as i32;
        k = char::from_u32(k as u32 + 1).unwrap();
    }
    s
}

fn main() {
    let s: i32 = sum(5 as char);
    // verus_assert(1);
}
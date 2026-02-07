extern "C" {
    static mut h: i32;
}

fn max_ptr(a: &i32, b: &i32) -> i32 {
    if *a < *b { *b } else { *a }
}

fn main() {
    unsafe { h = 42; }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(&a, &b);
    // verus_assert(1);
    // verus_assert(2);
}
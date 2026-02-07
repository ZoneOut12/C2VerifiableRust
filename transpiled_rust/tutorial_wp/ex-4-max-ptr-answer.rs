extern "C" {
    static mut h: i32;
}

fn max_ptr(a: &mut i32, b: &mut i32) {
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}

fn main() {
    unsafe {
        h = 42;
    }
    let mut a: i32 = 24;
    let mut b: i32 = 42;
    max_ptr(&mut a, &mut b);
    // verus_assert(1);
    // verus_assert(2);
}
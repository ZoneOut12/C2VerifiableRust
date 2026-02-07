extern "C" {
    static mut old: i32;
    static mut new: i32;
}

fn abs(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        -x
    }
}

fn distance(a: i32, b: i32) -> i32 {
    abs(b - a)
}

fn old_distance(a: i32, b: i32) -> i32 {
    if a < b {
        b - a
    } else {
        a - b
    }
}

fn test(a: i32, b: i32) {
    unsafe {
        old = old_distance(a, b);
        new = distance(a, b);
    }
    // verus_assert(1);
}
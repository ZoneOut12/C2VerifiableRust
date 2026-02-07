static mut h: i32 = 0;

fn max_ptr(a: Option<&i32>, b: Option<&i32>) -> i32 {
    if a.is_none() && b.is_none() {
        return i32::MIN;
    }
    if a.is_none() {
        return *b.unwrap();
    }
    if b.is_none() {
        return *a.unwrap();
    }
    let a_val = a.unwrap();
    let b_val = b.unwrap();
    if *a_val < *b_val {
        *b_val
    } else {
        *a_val
    }
}

fn main() {
    unsafe {
        h = 42;
    }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(Some(&a), Some(&b));
    // verus_assert(1);
    // verus_assert(2);
}
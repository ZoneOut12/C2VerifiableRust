fn add(p: &i32, q: &i32) -> i32 {
    *p + *q
}

fn main() {
    let a: i32 = 24;
    let b: i32 = 42;
    let mut x: i32;
    x = add(&a, &b);
    // verus_assert(1);
    // verus_assert(2);
    x = add(&a, &a);
    // verus_assert(3);
    // verus_assert(4);
}
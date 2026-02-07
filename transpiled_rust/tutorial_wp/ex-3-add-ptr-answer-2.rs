fn add(p: &i32, q: &i32, r: &mut i32) {
    *r = *p + *q;
}

fn main() {
    let a: i32 = 24;
    let b: i32 = 42;
    let mut x: i32 = 0;
    add(&a, &b, &mut x);
    // verus_assert(1);
    // verus_assert(2);
    add(&a, &a, &mut x);
    // verus_assert(3);
    // verus_assert(4);
}
fn add(a: &i32, b: &i32, r: &i32) -> i32 {
    *a + *b + *r
}

fn main() {
    let mut a: i32 = 24;
    let mut b: i32 = 32;
    let mut r: i32 = 12;
    let mut x: i32;
    x = add(&a, &b, &r);
    // verus_assert(1);
    // verus_assert(2);
}
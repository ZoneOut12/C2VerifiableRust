fn add(p: &i32, q: &i32) -> i32 {
    *p + *q
}

fn main() {
    let a: i32 = 24;
    let b: i32 = 32;
    let x: i32;
    x = add(&a, &b);
    // verus_assert(1)
    // verus_assert(2)
}
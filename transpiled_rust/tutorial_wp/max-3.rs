fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

fn foo() {
    let a: i32 = 42;
    let b: i32 = 37;
    let c: i32 = max(a, b);
    // verus_assert(1);
}
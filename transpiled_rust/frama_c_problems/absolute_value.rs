fn my_abs(val: i32) -> i32 {
    val.abs()
}

fn foo(a: i32) {
    let b: i32 = my_abs(-42);
    let c: i32 = my_abs(42);
    let d: i32 = my_abs(a);
}
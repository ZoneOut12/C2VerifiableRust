fn add_ten(mut a: i32) -> i32 {
    let mut i: i32 = 0;
    while i < 10 {
        a += 1;
        i += 1;
    }
    a
}
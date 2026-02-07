fn triangle(a: i32, b: i32, c: i32) -> i32 {
    if (a + b + c == 180) && a > 0 && b > 0 && c > 0 {
        1
    } else {
        0
    }
}

fn check_validity() {
    let res: i32 = triangle(90, 45, 45);
    // verus_assert(1);
}
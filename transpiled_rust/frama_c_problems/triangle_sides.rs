fn validts(a: i32, b: i32, c: i32) -> i32 {
    let mut valid: i32 = 0;
    if (a + b > c) && (a + c > b) && (b + c > a) {
        valid = 1;
    } else {
        valid = 0;
    }
    valid
}

fn test() {
    let valid: i32 = validts(2, 3, 4);
    // verus_assert(1);
}
fn leap(y: i32) -> i32 {
    (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0)) as i32
}

fn day_of(m: i32, y: i32) -> i32 {
    let days: [i32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    let n: i32 = days[(m - 1) as usize];
    if n == 28 {
        if leap(y) != 0 {
            return 29;
        } else {
            return 28;
        }
    }
    return n;
}
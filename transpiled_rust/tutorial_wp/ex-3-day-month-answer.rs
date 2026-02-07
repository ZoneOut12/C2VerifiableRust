fn day_of(m: i32) -> i32 {
    let days: &[i32] = &[31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    days[(m - 1) as usize]
}
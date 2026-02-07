fn sum_n(n: i32) -> i32 {
    if n < 1 {
        return 0;
    }
    let mut res: i32 = 0;
    let mut i: i32 = 1;
    while i <= n {
        res += i;
        i += 1;
    }
    res
}
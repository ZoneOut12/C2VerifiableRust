fn facto(n: i32) -> i32 {
    if n < 2 {
        return 1;
    }

    let mut res: i32 = 1;
    let mut i: i32 = 2;
    while i <= n {
        res = res * i;
        i += 1;
    }
    res
}
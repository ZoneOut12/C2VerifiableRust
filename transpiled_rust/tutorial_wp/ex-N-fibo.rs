fn helper(n: i32, p_1: i32, p_2: i32) {}

fn fibo(n: i32) -> i32 {
    if n < 2 {
        return 1;
    }

    let mut p_1: i32 = 1;
    let mut r: i32 = p_1 + 1;

    helper(2, p_1, 1);
    // verus_assert(1);

    let mut i: i32 = 2;
    while i < n {
        let x: i32 = r + p_1;
        helper(i + 1, r, p_1);
        p_1 = r;
        r = x;
        i += 1;
    }
    r
}
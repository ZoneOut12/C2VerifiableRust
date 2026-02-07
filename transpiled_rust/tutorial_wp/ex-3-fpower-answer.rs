fn power(x: i32, n: i32) -> i32 {
    let mut r: i32 = 1;
    let mut i: i32 = 1;
    while i <= n {
        r *= x;
        i += 1;
    }
    r
}

fn fast_power(x: u32, n: u32) -> u32 {
    let n_pre: u32 = n;
    let mut r: u32 = 1;
    let mut p: u32 = x;
    let mut n: u32 = n;
    while n > 0 {
        if n % 2 == 1 {
            // verus_assert(1);
            r = r * p;
        }
        p *= p;
        n /= 2;
    }
    // verus_assert(2);
    r
}
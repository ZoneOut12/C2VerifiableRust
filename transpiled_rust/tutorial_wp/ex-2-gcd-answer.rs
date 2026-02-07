fn gcd(a: i32, b: i32) -> i32 {
    let mut a: i32 = a;
    let mut b: i32 = b;
    while b != 0 {
        let t: i32 = b;
        b = a % b;
        a = t;
    }
    a
}
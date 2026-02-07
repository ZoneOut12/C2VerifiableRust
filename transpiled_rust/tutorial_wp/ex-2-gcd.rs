fn gcd(a: u32, b: u32) -> u32 {
    let a_pre: u32 = a;
    let b_pre: u32 = b;
    let mut a: u32 = a;
    let mut b: u32 = b;
    while b != 0 {
        let t: u32 = b;
        b = a % b;
        a = t;
    }
    return a;
}
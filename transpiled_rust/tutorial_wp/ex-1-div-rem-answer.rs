fn div_rem(x: u32, y: u32, q: &mut u32, r: &mut u32) {
    *q = x / y;
    *r = x % y;
}
fn main() {
    let mut x: i64 = 1;
    let mut y: i64 = 0;
    
    while y < 100000 {
        x = x + y;
        y = y + 1;
    }
    // verus_assert(1);
}
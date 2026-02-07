fn main() {
    let mut x: i32 = 1;
    let mut y: i32 = 0;

    while x <= 10 {
        y = 10 - x;
        x = x + 1;
    }

    // verus_assert(1);
}
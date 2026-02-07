fn main() {
    let mut x: i32 = 0;
    let mut size: i32 = 0;
    let mut y: i32 = 0;
    let mut z: i32 = 0;

    while x < size {
        x += 1;
        if z <= y {
            y = z;
        }
    }

    if size > 0 {
        // verus_assert(1);
    }
}
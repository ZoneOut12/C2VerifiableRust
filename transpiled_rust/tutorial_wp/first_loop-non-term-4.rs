fn main() {
    let mut i: i32 = 0;
    let mut h: i32 = 42;

    while i < 29 {
        i += 1;
    }

    if i < 30 {
        i += 1;

        if i == 30 {
            i = 42;
            h = 84;
        }
    }
    // verus_assert(1);
    // verus_assert(2);
}
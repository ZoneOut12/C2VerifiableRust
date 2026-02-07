fn foo() {
    let mut i: i32 = 0;
    let mut x: i32 = 0;

    while i < 20 {
        if i == 19 {
            x += 1;
            break;
        }
        i += 1;
    }
    // verus_assert(1);
    // verus_assert(2);
}
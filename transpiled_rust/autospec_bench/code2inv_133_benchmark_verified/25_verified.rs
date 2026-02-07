fn foo(mut x: i32) {
    while x > 0 {
        x = x - 1;
    }
    // verus_assert(1);
}
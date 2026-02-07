fn reset_1st_if_2nd_is_true(a: &mut i32, b: &i32) {
    if *b != 0 {
        *a = 0;
    }
}

fn main() {
    let mut a: i32 = 5;
    let x: i32 = 0;
    reset_1st_if_2nd_is_true(&mut a, &x);
    // verus_assert(1);
    // verus_assert(2);

    let b: i32 = 1;
    reset_1st_if_2nd_is_true(&mut a, &b);
    // verus_assert(3);
    // verus_assert(4);
}
const LARGE_INT: i32 = 10;

fn foo(mut k: i32) -> i32 {
    let mut i: i32;
    let mut j: i32;
    i = 1;
    let tmp: i32 = k;
    while i < LARGE_INT {
        i = i + 1;
        k = k - 1;
        // verus_assert(1);
    }
    0
}
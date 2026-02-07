fn distance(a: i32, b: i32) -> i32 {
    if a < b {
        b - a
    } else {
        a - b
    }
}

fn reset_1st_if_2nd_is_true(a: &mut i32, b: &i32) {
    if *b != 0 {
        *a = 0;
    }
}

fn day_of(m: i32) -> i32 {
    let days: [i32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    days[(m - 1) as usize]
}

fn max_ptr(a: &mut i32, b: &mut i32) {
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}
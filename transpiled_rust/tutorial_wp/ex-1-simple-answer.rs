fn max_ptr(a: &mut i32, b: &mut i32) {
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}

fn min_ptr(a: &mut i32, b: &mut i32) {
    max_ptr(b, a);
}

fn order_3_inc_min(a: &mut i32, b: &mut i32, c: &mut i32) {
    min_ptr(a, b);
    min_ptr(a, c);
    min_ptr(b, c);
}

fn incr_a_by_b(a: &mut i32, b: &i32) {
    *a += *b;
}
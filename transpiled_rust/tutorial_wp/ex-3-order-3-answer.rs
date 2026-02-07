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

fn order_3_inc_max(a: &mut i32, b: &mut i32, c: &mut i32) {
    max_ptr(c, b);
    max_ptr(c, a);
    max_ptr(b, a);
}

fn order_3_inc_min(a: &mut i32, b: &mut i32, c: &mut i32) {
    min_ptr(a, b);
    min_ptr(a, c);
    min_ptr(b, c);
}

fn order_3_dec_max(a: &mut i32, b: &mut i32, c: &mut i32) {
    max_ptr(a, b);
    max_ptr(a, c);
    max_ptr(b, c);
}

fn order_3_dec_min(a: &mut i32, b: &mut i32, c: &mut i32) {
    min_ptr(c, b);
    min_ptr(c, a);
    min_ptr(b, a);
}
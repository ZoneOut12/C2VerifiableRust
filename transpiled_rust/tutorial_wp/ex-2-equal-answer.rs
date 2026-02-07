fn equal(a_1: &[i32], a_2: &[i32], len: usize) -> i32 {
    let mut i: usize = 0;
    while i < len {
        if a_1[i] != a_2[i] {
            return 0;
        }
        i += 1;
    }
    1
}

fn different(a_1: &[i32], a_2: &[i32], len: usize) -> i32 {
    if equal(a_1, a_2, len) == 0 {
        1
    } else {
        0
    }
}
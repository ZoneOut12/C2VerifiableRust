fn vec_add(v1: &mut [i32], v2: &[i32], len: usize) {
    let mut i: usize = 0;
    while i < len {
        v1[i] += v2[i];
        i += 1;
    }
}

fn show_the_difference(v1: &mut [i32], v2: &[i32], len: usize) {
    vec_add(v1, v2, len);
}
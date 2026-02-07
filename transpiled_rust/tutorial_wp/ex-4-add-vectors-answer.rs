fn add_vectors(v_res: &mut [i32], v1: &[i32], v2: &[i32], len: usize) {
    let mut i: usize = 0;
    while i < len {
        v_res[i] = v1[i] + v2[i];
        i += 1;
    }
}
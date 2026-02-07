fn first_copy(src: &[i32], dst: &mut [i32], len: usize) {
    let mut i: usize = 0;
    while i < len {
        dst[i] = src[i];
        i += 1;
    }
}

fn copy(src: &[i32], dst: &mut [i32], len: usize) {
    let mut i: usize = 0;
    while i < len {
        dst[i] = src[i];
        i += 1;
    }
}

fn copy_backward(src: &[i32], dst: &mut [i32], len: usize) {
    let mut i: usize = len;
    while i > 0 {
        dst[i - 1] = src[i - 1];
        i -= 1;
    }
}
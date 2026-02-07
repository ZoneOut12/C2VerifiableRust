fn swap(a: &mut i32, b: &mut i32) {
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

fn reverse(array: &mut [i32], len: usize) {
    let mut i: usize = 0;
    while i < len / 2 {
        let right_i = len - i - 1;
        let (left, right) = array.split_at_mut(right_i);
        swap(&mut left[i], &mut right[0]);
        i += 1;
    }
}
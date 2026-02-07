fn swap(a: &mut i32, b: &mut i32) {
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

fn reverse(array: &mut [i32], len: usize) {
    let (left, right) = array.split_at_mut(len / 2);
    let mut i: usize = 0;
    while i < len / 2 {
        swap(&mut left[i], &mut right[right.len() - i - 1]);
        i += 1;
    }
}
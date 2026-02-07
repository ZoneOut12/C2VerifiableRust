fn fail_sort(a: &mut [i32], beg: usize, end: usize) {
    let mut i: usize = beg;
    while i < end {
        a[i] = 0;
        i += 1;
    }
}
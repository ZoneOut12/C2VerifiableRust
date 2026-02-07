fn min_idx_in(a: &mut [i32], beg: usize, end: usize) -> usize {
    let mut min_i: usize = beg;
    let mut i: usize = beg + 1;
    while i < end {
        if a[i] < a[min_i] {
            min_i = i;
        }
        i += 1;
    }
    min_i
}

fn swap(p: &mut i32, q: &mut i32) {
    let tmp: i32 = *p;
    *p = *q;
    *q = tmp;
}

fn sort(a: &mut [i32], beg: usize, end: usize) {
    let mut i: usize = beg;
    while i < end {
        let imin: usize = min_idx_in(a, i, end);
        if i != imin {
            if i < imin {
                let (left, right) = a.split_at_mut(imin);
                swap(&mut left[i], &mut right[0]);
            } else {
                let (left, right) = a.split_at_mut(i);
                swap(&mut left[imin], &mut right[0]);
            }
        }
        // verus_assert(1)
        i += 1;
    }
}
fn swap(a: &mut i32, b: &mut i32) {
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

fn abs_val(v: i32) -> i32 {
    if v >= 0 { v } else { -v }
}

fn max_int(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

fn min_int(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
}

fn clamp(v: i32, lo: i32, hi: i32) -> i32 {
    if v < lo { lo } else if v > hi { hi } else { v }
}

fn max3(a: i32, b: i32, c: i32) -> i32 {
    let mut m: i32 = a;
    if b > m { m = b; }
    if c > m { m = c; }
    m
}

fn sign(v: i32) -> i32 {
    if v > 0 { 1 } else if v < 0 { -1 } else { 0 }
}

fn array_min(a: &[i32], n: i32) -> i32 {
    let mut m: i32 = a[0];
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] < m { m = a[i as usize]; }
        i += 1;
    }
    m
}

fn array_max_index(a: &[i32], n: i32) -> i32 {
    let mut idx: i32 = 0;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] > a[idx as usize] { idx = i; }
        i += 1;
    }
    idx
}

fn array_min_index(a: &[i32], n: i32) -> i32 {
    let mut idx: i32 = 0;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] < a[idx as usize] { idx = i; }
        i += 1;
    }
    idx
}

fn array_sum(a: &[i32], n: i32) -> i32 {
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        s += a[i as usize];
        i += 1;
    }
    s
}

fn array_count(a: &[i32], n: i32, val: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == val { cnt += 1; }
        i += 1;
    }
    cnt
}

fn array_count_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] >= lo && a[i as usize] <= hi { cnt += 1; }
        i += 1;
    }
    cnt
}

fn all_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < lo || a[i as usize] > hi { return 0; }
        i += 1;
    }
    1
}

fn all_positive(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] <= 0 { return 0; }
        i += 1;
    }
    1
}

fn any_zero(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == 0 { return 1; }
        i += 1;
    }
    0
}

fn is_sorted_check(a: &[i32], n: i32) -> i32 {
    if n <= 1 { return 1; }
    let mut i: i32 = 0;
    while i < n - 1 {
        if a[i as usize] > a[(i + 1) as usize] { return 0; }
        i += 1;
    }
    1
}

fn array_equal(a: &[i32], b: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != b[i as usize] { return 0; }
        i += 1;
    }
    1
}

fn mismatch(a: &[i32], b: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != b[i as usize] { return i; }
        i += 1;
    }
    n
}

fn adjacent_find(a: &[i32], n: i32) -> i32 {
    if n <= 1 { return -1; }
    let mut i: i32 = 0;
    while i < n - 1 {
        if a[i as usize] == a[(i + 1) as usize] { return i; }
        i += 1;
    }
    -1
}

fn linear_search(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == val { return i; }
        i += 1;
    }
    -1
}

fn find_last(a: &[i32], n: i32, val: i32) -> i32 {
    let mut result: i32 = -1;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == val { result = i; }
        i += 1;
    }
    result
}

fn find_first_positive(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > 0 { return i; }
        i += 1;
    }
    -1
}

fn find_peak(a: &[i32], n: isize) -> isize {
    let mut i: isize = 1;
    while i < n - 1 {
        if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] {
            return i;
        }
        i += 1;
    }
    return -1;
}

fn find_valley(a: &[i32], n: isize) -> isize {
    let mut i: isize = 1;
    while i < n - 1 {
        if a[i as usize] < a[(i - 1) as usize] && a[i as usize] < a[(i + 1) as usize] {
            return i;
        }
        i += 1;
    }
    return -1;
}

fn max_increasing_length(a: &[i32], n: usize) -> usize {
    if n == 0 {
        return 0;
    }
    
    let mut max_len = 1;
    let mut cur_len = 1;
    
    let mut i = 1;
    while i < n {
        if a[i] > a[i - 1] {
            cur_len += 1;
            if cur_len > max_len {
                max_len = cur_len;
            }
        } else {
            cur_len = 1;
        }
        i += 1;
    }
    return max_len;
}

fn array_fill(a: &mut [i32], n: i32, val: i32) {
    let mut i: i32 = 0;
    while i < n {
        a[i as usize] = val;
        i += 1;
    }
}

fn array_copy(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = src[i as usize];
        i += 1;
    }
}

fn array_init_iota(a: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        a[i as usize] = i;
        i += 1;
    }
}

fn array_add_scalar(src: &[i32], dst: &mut [i32], n: i32, c: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = src[i as usize] + c;
        i += 1;
    }
}

fn array_negate(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = -src[i as usize];
        i += 1;
    }
}

fn array_replace(a: &mut [i32], n: i32, old_val: i32, new_val: i32) {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == old_val { a[i as usize] = new_val; }
        i += 1;
    }
}

fn prefix_sum(a: &[i32], out: &mut [i32], n: i32) {
    out[0] = a[0];
    let mut i: i32 = 1;
    while i < n {
        out[i as usize] = out[(i - 1) as usize] + a[i as usize];
        i += 1;
    }
}

fn array_reverse_copy(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = src[(n - 1 - i) as usize];
        i += 1;
    }
}

fn array_contains(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == val { return 1; }
        i += 1;
    }
    0
}

fn remove_element(a: &mut [i32], n: i32, val: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != val {
            a[j as usize] = a[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

fn count_zeros(a: &[i32], n: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == 0 { cnt += 1; }
        i += 1;
    }
    cnt
}

fn inner_product(a: &[i32], b: &[i32], n: i32) -> i32 {
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        // verus_assert(1);
        s += a[i as usize] * b[i as usize];
        i += 1;
    }
    s
}

fn find_min_in_range(a: &[i32], lo: i32, hi: i32) -> i32 {
    let mut idx: i32 = lo;
    let mut i: i32 = lo + 1;
    while i < hi {
        if a[i as usize] < a[idx as usize] { idx = i; }
        i += 1;
    }
    idx
}

fn find_second_max_index(a: &[i32], n: i32) -> i32 {
    let (mut first, mut second);
    if a[0] >= a[1] {
        first = 0; second = 1;
    } else {
        first = 1; second = 0;
    }
    let mut i: i32 = 2;
    while i < n {
        if a[i as usize] > a[first as usize] {
            second = first;
            first = i;
        } else if a[i as usize] > a[second as usize] {
            second = i;
        }
        i += 1;
    }
    second
}

fn all_distinct_sorted(a: &[i32], n: i32) -> i32 {
    if n <= 1 { return 1; }
    let mut i: i32 = 0;
    while i < n - 1 {
        if a[i as usize] == a[(i + 1) as usize] { return 0; }
        i += 1;
    }
    1
}

fn partition_binary(a: &mut [i32], n: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == 0 {
            let tmp = a[j as usize];
            a[j as usize] = a[i as usize];
            a[i as usize] = tmp;
            j += 1;
        }
        i += 1;
    }
    j
}

fn max_prefix_sum(a: &[i32], n: i32) -> i32 {
    let mut current: i32 = 0;
    let mut best: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        current += a[i as usize];
        if current > best { best = current; }
        i += 1;
    }
    best
}

fn array_map_abs(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        if src[i as usize] >= 0 {
            dst[i as usize] = src[i as usize];
        } else {
            dst[i as usize] = -src[i as usize];
        }
        i += 1;
    }
}

fn array_clamp_all(a: &mut [i32], n: i32, lo: i32, hi: i32) {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < lo {
            a[i as usize] = lo;
        } else if a[i as usize] > hi {
            a[i as usize] = hi;
        }
        i += 1;
    }
}
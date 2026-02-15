fn all_nonnegative(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < 0 {
            return 0;
        }
        i += 1;
    }
    1
}

fn all_nonpositive(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > 0 {
            return 0;
        }
        i += 1;
    }
    1
}

fn all_equal_to(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != val {
            return 0;
        }
        i += 1;
    }
    1
}

fn all_greater_than(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] <= val {
            return 0;
        }
        i += 1;
    }
    1
}

fn is_strictly_increasing(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n - 1 {
        if a[i as usize] >= a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

fn is_strictly_decreasing(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n - 1 {
        if a[i as usize] <= a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

fn is_constant(a: &[i32], n: i32) -> i32 {
    let v: i32 = a[0];
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] != v {
            return 0;
        }
        i += 1;
    }
    1
}

fn no_duplicates_sorted(a: &[i32], n: i32) -> i32 {
    if n <= 1 {
        return 1;
    }
    let mut i: i32 = 0;
    while i < n - 1 {
        if a[i as usize] == a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

fn all_in_bounds(a: &[i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < lo || a[i as usize] > hi {
            return 0;
        }
        i += 1;
    }
    1
}

fn count_positive(a: &[i32], n: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_negative(a: &[i32], n: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_greater_than(a: &[i32], n: i32, val: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_not_equal(a: &[i32], n: i32, val: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_less_than(a: &[i32], n: i32, val: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_sign_changes(a: &[i32], n: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n {
        if (a[(i - 1) as usize] > 0 && a[i as usize] < 0) || (a[(i - 1) as usize] < 0 && a[i as usize] > 0) {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_value_changes(a: &[i32], n: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] != a[(i - 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn find_first_ge(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] >= val {
            return i;
        }
        i += 1;
    }
    -1
}

fn find_first_le(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] <= val {
            return i;
        }
        i += 1;
    }
    -1
}

fn find_first_zero(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == 0 {
            return i;
        }
        i += 1;
    }
    -1
}

fn find_first_negative(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < 0 {
            return i;
        }
        i += 1;
    }
    -1
}

fn find_first_ne(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != val {
            return i;
        }
        i += 1;
    }
    -1
}

fn find_last_gt(a: &[i32], n: i32, val: i32) -> i32 {
    let mut result: i32 = -1;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > val {
            result = i;
        }
        i += 1;
    }
    result
}

fn find_first_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] >= lo && a[i as usize] <= hi {
            return i;
        }
        i += 1;
    }
    n
}

fn count_outside_range(a: &[i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < lo || a[i as usize] > hi {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn is_non_increasing(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 1;
    while i < n {
        if a[(i - 1) as usize] < a[i as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

fn all_less_than(a: &[i32], n: i32, val: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] >= val {
            return 0;
        }
        i += 1;
    }
    1
}

fn none_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] >= lo && a[i as usize] <= hi {
            return 0;
        }
        i += 1;
    }
    1
}

fn saturate_copy(src: &[i32], dst: &mut [i32], n: i32, lo: i32, hi: i32) {
    let mut i: i32 = 0;
    while i < n {
        if src[i as usize] < lo {
            dst[i as usize] = lo;
        } else if src[i as usize] > hi {
            dst[i as usize] = hi;
        } else {
            dst[i as usize] = src[i as usize];
        }
        i += 1;
    }
}

fn shift_copy(src: &[i32], dst: &mut [i32], n: i32, c: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = src[i as usize] + c;
        i += 1;
    }
}

fn scale_copy(src: &[i32], dst: &mut [i32], n: i32, c: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = src[i as usize] * c;
        i += 1;
    }
}

fn partition(a: &mut [i32], n: i32, pivot: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < pivot {
            let tmp: i32 = a[j as usize];
            a[j as usize] = a[i as usize];
            a[i as usize] = tmp;
            j += 1;
        }
        i += 1;
    }
    j
}

fn segregate_greater(a: &mut [i32], n: i32, val: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > val {
            let tmp: i32 = a[j as usize];
            a[j as usize] = a[i as usize];
            a[i as usize] = tmp;
            j += 1;
        }
        i += 1;
    }
    j
}

fn segregate_negative(a: &mut [i32], n: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < 0 {
            let tmp: i32 = a[j as usize];
            a[j as usize] = a[i as usize];
            a[i as usize] = tmp;
            j += 1;
        }
        i += 1;
    }
    j
}

fn segregate_zeros(a: &mut [i32], n: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] == 0 {
            let tmp: i32 = a[j as usize];
            a[j as usize] = a[i as usize];
            a[i as usize] = tmp;
            j += 1;
        }
        i += 1;
    }
    j
}

fn partition_le(a: &mut [i32], n: i32, pivot: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] <= pivot {
            let tmp: i32 = a[j as usize];
            a[j as usize] = a[i as usize];
            a[i as usize] = tmp;
            j += 1;
        }
        i += 1;
    }
    j
}

fn pointwise_max(a: &[i32], b: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = if a[i as usize] >= b[i as usize] { a[i as usize] } else { b[i as usize] };
        i += 1;
    }
}

fn pointwise_min(a: &[i32], b: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = if a[i as usize] <= b[i as usize] { a[i as usize] } else { b[i as usize] };
        i += 1;
    }
}

fn threshold_filter(src: &[i32], dst: &mut [i32], n: i32, threshold: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = if src[i as usize] >= threshold { 1 } else { 0 };
        i += 1;
    }
}

fn map_square(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = src[i as usize] * src[i as usize];
        i += 1;
    }
}

fn sign_array(a: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > 0 {
            dst[i as usize] = 1;
        } else if a[i as usize] < 0 {
            dst[i as usize] = -1;
        } else {
            dst[i as usize] = 0;
        }
        i += 1;
    }
}

fn relu(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = if src[i as usize] >= 0 { src[i as usize] } else { 0 };
        i += 1;
    }
}

fn masked_copy(src: &[i32], mask: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        dst[i as usize] = if mask[i as usize] != 0 { src[i as usize] } else { 0 };
        i += 1;
    }
}

fn compact_positives(src: &[i32], dst: &mut [i32], n: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if src[i as usize] > 0 {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

fn compact_nonzero(src: &[i32], dst: &mut [i32], n: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if src[i as usize] != 0 {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

fn compact_greater(src: &[i32], dst: &mut [i32], n: i32, val: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if src[i as usize] > val {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

fn compact_in_range(src: &[i32], dst: &mut [i32], n: i32, lo: i32, hi: i32) -> i32 {
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if src[i as usize] >= lo && src[i as usize] <= hi {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

fn count_distinct_sorted(a: &[i32], n: i32) -> i32 {
    if n == 0 {
        return 0;
    }
    let mut cnt: i32 = 1;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] != a[(i - 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn hamming_distance(a: &[i32], b: &[i32], n: i32) -> i32 {
    let mut d: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != b[i as usize] {
            d += 1;
        }
        i += 1;
    }
    d
}

fn longest_plateau(a: &[i32], n: i32) -> i32 {
    if n == 0 {
        return 0;
    }
    let mut best: i32 = 1;
    let mut run: i32 = 1;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] == a[(i - 1) as usize] {
            run += 1;
        } else {
            run = 1;
        }
        if run > best {
            best = run;
        }
        i += 1;
    }
    best
}

fn count_local_maxima(a: &[i32], n: i32) -> i32 {
    if n <= 2 {
        return 0;
    }
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n - 1 {
        if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn count_local_minima(a: &[i32], n: i32) -> i32 {
    if n <= 2 {
        return 0;
    }
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n - 1 {
        if a[i as usize] < a[(i - 1) as usize] && a[i as usize] < a[(i + 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

fn pointwise_le(a: &[i32], b: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > b[i as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

fn classify_range(a: &[i32], dst: &mut [i32], n: i32, lo: i32, hi: i32) {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < lo {
            dst[i as usize] = 0;
        } else if a[i as usize] > hi {
            dst[i as usize] = 2;
        } else {
            dst[i as usize] = 1;
        }
        i += 1;
    }
}

fn argmax(a: &[i32], n: i32) -> i32 {
    let mut idx: i32 = 0;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] > a[idx as usize] {
            idx = i;
        }
        i += 1;
    }
    idx
}

fn argmin(a: &[i32], n: i32) -> i32 {
    let mut idx: i32 = 0;
    let mut i: i32 = 1;
    while i < n {
        if a[i as usize] < a[idx as usize] {
            idx = i;
        }
        i += 1;
    }
    idx
}

fn adjacent_difference(src: &[i32], dst: &mut [i32], n: i32) {
    dst[0] = src[0];
    let mut i: i32 = 1;
    while i < n {
        dst[i as usize] = src[i as usize] - src[(i - 1) as usize];
        i += 1;
    }
}

fn fill_countdown(a: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        a[i as usize] = n - 1 - i;
        i += 1;
    }
}

fn adjacent_sum_copy(src: &[i32], dst: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n - 1 {
        dst[i as usize] = src[i as usize] + src[(i + 1) as usize];
        i += 1;
    }
    dst[(n - 1) as usize] = src[(n - 1) as usize];
}

fn cap_at(a: &mut [i32], n: i32, cap: i32) {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] > cap {
            a[i as usize] = cap;
        }
        i += 1;
    }
}

fn floor_at(a: &mut [i32], n: i32, floor_val: i32) {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] < floor_val {
            a[i as usize] = floor_val;
        }
        i += 1;
    }
}
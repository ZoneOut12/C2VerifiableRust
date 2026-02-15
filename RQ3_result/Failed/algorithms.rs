verus! {

pub mod libmath {
    #[allow(unused_imports)]


    use vstd::math::*;
    use vstd::prelude::*;
    #[allow(unused_imports)]
    use vstd::slice::*;

    #[verifier::external_fn_specification]
    pub fn i32_abs(x: i32) -> (result: i32)
        ensures
            result >= 0,
            result == if x < 0 {
                -x as int
            } else {
                x as int
            },
    {
        x.abs()
    }

}

} // verus!
#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::slice::*;

verus! {

pub open spec fn sorted(a: &[i32], lo: int, hi: int) -> bool {
    forall|i: int, j: int|
        (lo <= i <= j < hi) as int != 0 ==> (a@[(i) as int] <= a@[(j) as int]) as int != 0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn swap(a: &mut i32, b: &mut i32)
    requires
        true && true,
        true,
    ensures
        ((a)@) == ((old(b))@),
        ((b)@) == ((old(a))@),
{
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn abs_val(v: i32) -> (result: i32)
    requires
        v > i32::MIN,
    ensures
        result >= 0,
        (v >= 0) as int != 0 ==> (result == v) as int != 0,
        (v < 0) as int != 0 ==> (result == -v) as int != 0,
{
    if v >= 0 {
        v
    } else {
        -v
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_int(a: i32, b: i32) -> (result: i32)
    ensures
        result >= a && result >= b,
        result == a || result == b,
{
    if a >= b {
        a
    } else {
        b
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn min_int(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b,
        result == a || result == b,
{
    if a <= b {
        a
    } else {
        b
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn clamp(v: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        lo <= hi,
    ensures
        lo <= result <= hi,
        (v < lo) as int != 0 ==> (result == lo) as int != 0,
        (v > hi) as int != 0 ==> (result == hi) as int != 0,
        (lo <= v <= hi) as int != 0 ==> (result == v) as int != 0,
{
    if v < lo {
        lo
    } else if v > hi {
        hi
    } else {
        v
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max3(a: i32, b: i32, c: i32) -> (result: i32)
    ensures
        result >= a && result >= b && result >= c,
        result == a || result == b || result == c,
{
    let mut m: i32 = a;
    if b > m {
        m = b;
    }
    if c > m {
        m = c;
    }
    m
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sign(v: i32) -> (result: i32)
    ensures
        ((v > 0) as int != 0 ==> (result == 1) as int != 0),
        ((v == 0) as int != 0 ==> (result == 0) as int != 0),
        ((v < 0) as int != 0 ==> (result == -1) as int != 0),
{
    if v > 0 {
        1
    } else if v < 0 {
        -1
    } else {
        0
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_min(a: &[i32], n: i32) -> (result: i32)
    requires
        n > 0 && n <= i32::MAX,
        a@.len() >= n - 1 + 1,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (result <= a@[(k) as int]) as int != 0,
        exists|k: int| 0 <= k < n && a@[(k) as int] == result,
{
    let mut m: i32 = a[0];
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (m <= a@[(k) as int]) as int != 0,
            exists|k: int| 0 <= k < i && a@[(k) as int] == m,
        decreases n - i,
    {
        if a[i as usize] < m {
            m = a[i as usize];
        }
        i += 1;
    }
    m
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_max_index(a: &[i32], n: i32) -> (result: i32)
    requires
        n > 0 && n <= i32::MAX,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result < n,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] <= a@[(result) as int]) as int != 0,
{
    let mut idx: i32 = 0;
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            0 <= idx < i,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= a@[(idx) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] > a[idx as usize] {
            idx = i;
        }
        i += 1;
    }
    idx
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_min_index(a: &[i32], n: i32) -> (result: i32)
    requires
        n > 0 && n <= i32::MAX,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result < n,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(result) as int] <= a@[(k) as int]) as int != 0,
{
    let mut idx: i32 = 0;
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            0 <= idx < i,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(idx) as int] <= a@[(k) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] < a[idx as usize] {
            idx = i;
        }
        i += 1;
    }
    idx
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_sum(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0 && n <= 100000,
        a@.len() >= n - 1 + 1,
        forall|k: int| (0 <= k < n) as int != 0 ==> (-10000 <= a@[(k) as int] <= 10000) as int != 0, 
    ensures
        -10000 * n <= result <= 10000 * n,
{
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            -10000 * i <= s <= 10000 * i,
        decreases n - i,
    {
        s += a[i as usize];
        i += 1;
    }
    s
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_count(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] == val) as int != 0 ==> (result
                > 0) as int != 0)) as int != 0,
{
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= cnt <= i,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] == val) as int != 0 ==> (cnt
                    > 0) as int != 0)) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_count_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        lo <= hi,
    ensures
        0 <= result <= n,
{
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= cnt <= i,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((lo <= a@[(k) as int] <= hi) as int != 0 ==> (cnt 
                    > 0) as int != 0)) as int != 0,
        decreases n - i,
    {
        if a[i as usize] >= lo && a[i as usize] <= hi {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (lo <= a@[(k) as int] <= hi) as int != 0) as int != 0, 
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n && (a@[(k) as int] < lo || a@[(k) as int] > hi)) as int != 0,
        result == 0 || result == 1,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (lo <= a@[(k) as int] <= hi) as int != 0, 
        decreases n - i,
    {
        if a[i as usize] < lo || a[i as usize] > hi {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_positive(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] > 0) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] <= 0) as int
            != 0,
        result == 0 || result == 1,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] > 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] <= 0 {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn any_zero(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        (result == 1) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] == 0) as int
            != 0,
        (result == 0) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] != 0) as int != 0) as int != 0,
        result == 0 || result == 1,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] != 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == 0 {
            return 1;
        }
        i += 1;
    }
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_sorted_check(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        (result == 1) as int != 0 ==> ((sorted(a, 0 as int, n as int))) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n - 1 && a@[(k) as int] > a@[(k + 1) as int]) as int != 0, 
        result == 0 || result == 1,
{
    if n <= 1 {
        return 1;
    }
    let mut i: i32 = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|p: int, q: int|
                (0 <= p <= q <= i) as int != 0 ==> (a@[(p) as int] <= a@[(q) as int]) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] > a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_equal(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
    ensures
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] == b@[(k) as int]) as int != 0) as int
            != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n && a@[(k) as int] != b@[(k) as int]) as int != 0,
        result == 0 || result == 1,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] == b@[(k) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != b[i as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mismatch(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] == b@[(k) as int]) as int != 0,
        (result < n) as int != 0 ==> (a@[(result) as int] != b@[(result) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] == b@[(k) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != b[i as usize] {
            return i;
        }
        i += 1;
    }
    n
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn adjacent_find(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n - 1,
        (result >= 0) as int != 0 ==> (a@[(result) as int] == a@[(result + 1) as int]) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n - 1) as int != 0 ==> (a@[(k) as int] != a@[(k + 1) as int]) as int  
                != 0) as int != 0,
{
    if n <= 1 {
        return -1;
    }
    let mut i: i32 = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] != a@[(k + 1) as int]) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] == a[(i + 1) as usize] {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn linear_search(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] == val) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] != val) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] != val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == val {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_last(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] == val) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (result < k < n) as int != 0 ==> (a@[(k) as int] != val) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] != val) as int != 0) as int != 0,
{
    let mut result: i32 = -1;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            -1 <= result < i,
            (result >= 0) as int != 0 ==> (a@[(result) as int] == val) as int != 0,
            (result >= 0) as int != 0 ==> (forall|k: int|
                (result < k < i) as int != 0 ==> (a@[(k) as int] != val) as int != 0) as int != 0,
            (result == -1) as int != 0 ==> (forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] != val) as int != 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == val {
            result = i;
        }
        i += 1;
    }
    result
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_positive(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] > 0) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] <= 0) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] <= 0) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] > 0 {
            return i;
        }
        i += 1;
    }
    -1
}


#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_peak(a: &[i32], n: isize) -> (result: isize)
    requires
        n >= 3,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> ((1 <= result <= n - 2 && a@[(result) as int] > a@[(result
            - 1) as int] && a@[(result) as int] > a@[(result + 1) as int])) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (1 <= k <= n - 2) as int != 0 ==> ((a@[(k) as int] <= a[(k - 1) as int] || a@[(
            k) as int] <= a@[(k + 1) as int])) as int != 0) as int != 0,
{
    let mut i: isize = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1,
            forall|k: int|
                (1 <= k < i) as int != 0 ==> ((a@[(k) as int] <= a@[(k - 1) as int] || a@[(
                k) as int] <= a@[(k + 1) as int])) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] {
            return i;
        }
        i += 1;
    }
    return -1;
}

pub open spec fn find_valley_helper(a: &[i32], i: int) -> bool
{
    a[i] >= a[i - 1]
}


#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_valley(a: &[i32], n: isize) -> (result: isize)
    requires
        n >= 3,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> ((1 <= result <= n - 2 && a@[(result) as int] < a@[(result
            - 1) as int] && a@[(result) as int] < a@[(result + 1) as int])) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (1 <= k <= n - 2) as int != 0 ==> ((a@[(
            k) as int] >= a@[(k - 1) as int] || a@[(
            k) as int] >= a@[(k + 1) as int])) as int != 0) as int != 0,
{
    let mut i: isize = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1,
            forall|k: int|
                (1 <= k < i) as int != 0 ==> ((a@[(k) as int] >= a@[(k - 1) as int] || a@[(
                k) as int] >= a@[(k + 1) as int])) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] < a[(i - 1) as usize] && a[i as usize] < a[(i + 1) as usize] {
            return i;
        }
        i += 1;
    }
    return -1;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_increasing_length(a: &[i32], n: usize) -> (result: usize)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        (n > 0) as int != 0 ==> (result >= 1) as int != 0,
{
    if n == 0 {
        return 0;
    }
    let mut max_len = 1;
    let mut cur_len = 1;

    let mut i = 1;
    while i < n
        invariant
            1 <= i <= n,
            1 <= cur_len <= i,
            1 <= max_len <= i,
            max_len >= cur_len,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_fill(a: &mut [i32], n: i32, val: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] == val) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] == val) as int != 0,
        decreases n - i,
    {
        a[i as usize] = val;
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_copy(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int]) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = src[i as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_init_iota(a: &mut [i32], n: i32)
    requires
        n >= 0 && n <= i32::MAX,
        old(a)@.len() >= n - 1 + 1,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] == k) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] == k) as int != 0,
        decreases n - i,
    {
        a[i as usize] = i;
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_add_scalar(src: &[i32], dst: &mut [i32], n: i32, c: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (i32::MIN <= src@[(k) as int] + c && src@[(k) as int] + c
                <= i32::MAX) as int != 0,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] + c) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] + c) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = src[i as usize] + c;
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_negate(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int| (0 <= k < n) as int != 0 ==> (src@[(k) as int] > i32::MIN) as int != 0,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == -src@[(k) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == -src@[(k) as int]) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = -src[i as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_replace(a: &mut [i32], n: i32, old_val: i32, new_val: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
        old_val != new_val,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] != old_val) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] != old_val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == old_val {
            a[i as usize] = new_val;
        }
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn prefix_sum(a: &[i32], out: &mut [i32], n: i32)
    requires
        n > 0 && n <= 10000,
        a@.len() >= n - 1 + 1,
        old(out)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (-100000 <= a@[(k) as int] <= 100000) as int != 0,
    ensures
        out@[(0) as int] == a@[(0) as int],
        forall|k: int|
            (1 <= k < n) as int != 0 ==> (out@[(k) as int] == out@[(k - 1) as int] + a@[(
            k) as int]) as int != 0,
{
    out[0] = a[0];
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            out@[(0) as int] == a@[(0) as int],
            forall|k: int|
                (1 <= k < i) as int != 0 ==> (out@[(k) as int] == out@[(k - 1) as int] + a@[(
                k) as int]) as int != 0,
            -100000 * i <= out@[(i - 1) as int] <= 100000 * i,
        decreases n - i,
    {
        out[i as usize] = out[(i - 1) as usize] + a[i as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_reverse_copy(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(n - 1 - k) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(n - 1 - k) as int]) as int
                    != 0,
        decreases n - i,
    {
        dst[i as usize] = src[(n - 1 - i) as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_contains(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] == val) as int
            != 0,
        (result == 0) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] != val) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] != val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == val {
            return 1;
        }
        i += 1;
    }
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn remove_element(a: &mut [i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] != val) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] != val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != val {
            a[j as usize] = a[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_zeros(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
{
    let mut cnt: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= cnt <= i,
        decreases n - i,
    {
        if a[i as usize] == 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inner_product(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0 && n <= 10000,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
        forall|k: int| (0 <= k < n) as int != 0 ==> (0 <= a@[(k) as int] <= 100) as int != 0,
        forall|k: int| (0 <= k < n) as int != 0 ==> (0 <= b@[(k) as int] <= 100) as int != 0,
    ensures
        0 <= result <= 10000 * n,
{
    let mut s: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= s <= 10000 * i,
        decreases n - i,
    {
        assert(0 <= a@[(i) as int] * b@[(i) as int] <= 10000);
        s += a[i as usize] * b[i as usize];
        i += 1;
    }
    s
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_min_in_range(a: &[i32], lo: i32, hi: i32) -> (result: i32)
    requires
        0 < lo < hi,
        a@.len() >= hi - 1 + 1,
    ensures
        lo <= result < hi,
        forall|k: int|
            (lo <= k < hi) as int != 0 ==> (a@[(result) as int] <= a@[(k) as int]) as int != 0,
{
    let mut idx: i32 = lo;
    let mut i: i32 = lo + 1;
    while i < hi
        invariant
            lo + 1 <= i <= hi,
            lo <= idx < i,
            forall|k: int|
                (lo <= k < i) as int != 0 ==> (a@[(idx) as int] <= a@[(k) as int]) as int != 0,
        decreases hi - i,
    {
        if a[i as usize] < a[idx as usize] {
            idx = i;
        }
        i += 1;
    }
    idx
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_second_max_index(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 2,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result < n,
        exists|k: int| 0 <= k < n && k != result && a@[(k) as int] >= a@[(result) as int],
{
    let (mut first, mut second);
    if a[0] >= a[1] {
        first = 0;
        second = 1;
    } else {
        first = 1;
        second = 0;
    }
    let mut i: i32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            0 <= first < i && 0 <= second < i,
            first != second,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= a@[(first) as int]) as int != 0,
            forall|k: int|
                (0 <= k < i && k != first) as int != 0 ==> (a@[(k) as int] <= a@[(
                second) as int]) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_distinct_sorted(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        (sorted(a, 0 as int, n as int)),
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|p: int, q: int|
            (0 <= p < q < n) as int != 0 ==> (a@[(p) as int] < a@[(q) as int]) as int != 0) as int
            != 0,
        (result == 0) as int != 0 ==> ((n >= 2 && exists|k: int|
            0 <= k < n - 1 && a@[(k) as int] == a@[(k + 1) as int])) as int != 0,
{
    if n <= 1 {
        return 1;
    }
    let mut i: i32 = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|p: int, q: int|
                (0 <= p < q <= i) as int != 0 ==> (a@[(p) as int] < a@[(q) as int]) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] == a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn partition_binary(a: &mut [i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (old(a)@[(k) as int] == 0 || old(a)@[(k) as int]
                == 1) as int != 0,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] == 0) as int != 0,
        forall|k: int| (result <= k < n) as int != 0 ==> (a@[(k) as int] == 1) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] == 0) as int != 0,
            forall|k: int| (j <= k < i) as int != 0 ==> (a@[(k) as int] == 1) as int != 0,
            forall|k: int|
                (i <= k < n) as int != 0 ==> ((a@[(k) as int] == 0 || a@[(k) as int] == 1)) as int
                    != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_prefix_sum(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        forall|k: int| (0 <= k < n) as int != 0 ==> (0 <= a@[(k) as int] <= 10000) as int != 0,
        n <= 10000,
    ensures
        0 <= result,
{
    let mut current: i32 = 0;
    let mut best: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= current <= 10000 * i,
            0 <= best <= 10000 * i,
            best >= current || best >= 0,
        decreases n - i,
    {
        current += a[i as usize];
        if current > best {
            best = current;
        }
        i += 1;
    }
    best
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_map_abs(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int| (0 <= k < n) as int != 0 ==> (src@[(k) as int] > i32::MIN) as int != 0,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] >= 0) as int != 0 ==> (dst@[(k) as int]
                == src@[(k) as int]) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] < 0) as int != 0 ==> (dst@[(k) as int]
                == -src@[(k) as int]) as int != 0)) as int != 0,
        forall|k: int| (0 <= k < n) as int != 0 ==> (dst@[(k) as int] >= 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] >= 0) as int != 0 ==> (dst@[(
                k) as int] == src@[(k) as int]) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] < 0) as int != 0 ==> (dst@[(
                k) as int] == -src@[(k) as int]) as int != 0)) as int != 0,
            forall|k: int| (0 <= k < i) as int != 0 ==> (dst@[(k) as int] >= 0) as int != 0,
        decreases n - i,
    {
        if src[i as usize] >= 0 {
            dst[i as usize] = src[i as usize];
        } else {
            dst[i as usize] = -src[i as usize];
        }
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_clamp_all(a: &mut [i32], n: i32, lo: i32, hi: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
        lo <= hi,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (lo <= a@[(k) as int] <= hi) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (lo <= a@[(k) as int] <= hi) as int != 0,
        decreases n - i,
    {
        if a[i as usize] < lo {
            a[i as usize] = lo;
        } else if a[i as usize] > hi {
            a[i as usize] = hi;
        }
        i += 1;
    }
}

fn main() {
}

} // verus!

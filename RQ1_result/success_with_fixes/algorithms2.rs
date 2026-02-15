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
fn all_nonnegative(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] < 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] < 0 {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_nonpositive(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] <= 0) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] > 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] > 0 {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_equal_to(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] == val) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> ((n == 0 || exists|k: int|
            0 <= k < n && a@[(k) as int] != val)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] == val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != val {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_greater_than(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] > val) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] <= val) as int
            != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] > val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] <= val {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_strictly_increasing(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n - 1) as int != 0 ==> (#[trigger] a@[(k) as int] < a@[(k + 1) as int]) as int
                != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n - 1 && #[trigger] a@[(k) as int] >= a@[(k + 1) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (#[trigger] a@[(k) as int] < a@[(k + 1) as int]) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] >= a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_strictly_decreasing(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n - 1) as int != 0 ==> (#[trigger] a@[(k) as int] > a@[(k + 1) as int]) as int
                != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n - 1 && #[trigger] a@[(k) as int] <= a@[(k + 1) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (#[trigger] a@[(k) as int] > a@[(k + 1) as int]) as int != 0,
        decreases n - 1 - i,
    {
        if a[i as usize] <= a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_constant(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (#[trigger] a@[(k) as int] == a@[(0) as int]) as int != 0) as int
            != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n && #[trigger] a@[(k) as int] != a@[(0) as int]) as int != 0,
{
    let v: i32 = a[0];
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            v == a@[(0) as int],
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] == v) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != v {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn no_duplicates_sorted(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        (sorted(a, 0 as int, n as int)),
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|p: int, q: int|
            (0 <= p < q < n) as int != 0 ==> (a@[(p) as int] < a@[(q) as int]) as int != 0) as int
            != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n - 1 && #[trigger] a@[(k) as int] == a@[(k + 1) as int]) as int != 0,
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
fn all_in_bounds(a: &[i32], n: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (lo <= #[trigger] a@[(k) as int] <= hi) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n && (#[trigger] a@[(k) as int] < lo || a@[(k) as int] > hi)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (lo <= #[trigger] a@[(k) as int] <= hi) as int != 0,
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
fn count_positive(a: &[i32], n: i32) -> (result: i32)
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
        if a[i as usize] > 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_negative(a: &[i32], n: i32) -> (result: i32)
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
        if a[i as usize] < 0 {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_greater_than(a: &[i32], n: i32, val: i32) -> (result: i32)
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
        if a[i as usize] > val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_not_equal(a: &[i32], n: i32, val: i32) -> (result: i32)
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
        if a[i as usize] != val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_less_than(a: &[i32], n: i32, val: i32) -> (result: i32)
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
        if a[i as usize] < val {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_sign_changes(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n - 1,
{
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            0 <= cnt <= i - 1,
        decreases n - i,
    {
        if (a[(i - 1) as usize] > 0 && a[i as usize] < 0) || (a[(i - 1) as usize] < 0
            && a[i as usize] > 0) {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_value_changes(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n - 1,
{
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            0 <= cnt <= i - 1,
        decreases n - i,
    {
        if a[i as usize] != a[(i - 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_ge(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] >= val) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] < val) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] < val) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] < val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] >= val {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_le(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] <= val) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] > val) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] > val) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] > val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] <= val {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_zero(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] == 0) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] != 0) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] != 0) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] != 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] == 0 {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_negative(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] < 0) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] < 0 {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_ne(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] != val) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> (a@[(k) as int] == val) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] == val) as int != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] == val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != val {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_last_gt(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        -1 <= result < n,
        (result >= 0) as int != 0 ==> (a@[(result) as int] > val) as int != 0,
        (result >= 0) as int != 0 ==> (forall|k: int|
            (result < k < n) as int != 0 ==> (a@[(k) as int] <= val) as int != 0) as int != 0,
        (result == -1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] <= val) as int != 0) as int != 0,
{
    let mut result: i32 = -1;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            -1 <= result < i,
            (result >= 0) as int != 0 ==> (a@[(result) as int] > val) as int != 0,
            (result >= 0) as int != 0 ==> (forall|k: int|
                (result < k < i) as int != 0 ==> (a@[(k) as int] <= val) as int != 0) as int != 0,
            (result == -1) as int != 0 ==> (forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= val) as int != 0) as int != 0,
        decreases n - i,
    {
        if a[i as usize] > val {
            result = i;
        }
        i += 1;
    }
    result
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn find_first_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        n >= 0,
        lo <= hi,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        (result < n) as int != 0 ==> (lo <= a@[(result) as int] <= hi) as int != 0,
        (result < n) as int != 0 ==> (forall|k: int|
            (0 <= k < result) as int != 0 ==> ((!(((lo <= #[trigger] a@[(k) as int] <= hi)) as int
                != 0))) as int != 0) as int != 0,
        (result == n) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> ((!(((lo <= #[trigger] a@[(k) as int] <= hi)) as int != 0))) as int
                != 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> ((!(((lo <= #[trigger] a@[(k) as int] <= hi)) as int
                    != 0))) as int != 0,
        decreases n - i,
    {
        if a[i as usize] >= lo && a[i as usize] <= hi {
            return i;
        }
        i += 1;
    }
    n
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_outside_range(a: &[i32], n: i32, lo: i32, hi: i32) -> (result: i32)
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
        if a[i as usize] < lo || a[i as usize] > hi {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_non_increasing(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 1,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n - 1) as int != 0 ==> (#[trigger] a@[(k) as int] >= a@[(k + 1) as int]) as int
                != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n - 1 && #[trigger] a@[(k) as int] < a@[(k + 1) as int]) as int != 0,
{
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            forall|k: int|
                (0 <= k < i - 1) as int != 0 ==> (#[trigger] a@[(k) as int] >= a@[(k + 1) as int]) as int != 0,
        decreases n - i,
    {
        if a[(i - 1) as usize] < a[i as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn all_less_than(a: &[i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] < val) as int != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int| 0 <= k < n && a@[(k) as int] >= val) as int
            != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] < val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] >= val {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn none_in_range(a: &[i32], n: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> ((!(((lo <= #[trigger] a@[(k) as int] <= hi)) as int != 0))) as int
                != 0) as int != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n && lo <= #[trigger] a@[(k) as int] <= hi) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> ((!(((lo <= #[trigger] a@[(k) as int] <= hi)) as int
                    != 0))) as int != 0,
        decreases n - i,
    {
        if a[i as usize] >= lo && a[i as usize] <= hi {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn saturate_copy(src: &[i32], dst: &mut [i32], n: i32, lo: i32, hi: i32)
    requires
        n >= 0,
        lo <= hi,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] < lo) as int != 0 ==> (dst@[(k) as int]
                == lo) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] > hi) as int != 0 ==> (dst@[(k) as int]
                == hi) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((lo <= src@[(k) as int] <= hi) as int != 0 ==> (dst@[(
            k) as int] == src@[(k) as int]) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] < lo) as int != 0 ==> (dst@[(
                k) as int] == lo) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] > hi) as int != 0 ==> (dst@[(
                k) as int] == hi) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((lo <= src@[(k) as int] <= hi) as int != 0 ==> (
                dst@[(k) as int] == src@[(k) as int]) as int != 0)) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn shift_copy(src: &[i32], dst: &mut [i32], n: i32, c: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (-1000000 <= #[trigger] src@[(k) as int] <= 1000000) as int != 0,
        -1000 <= c <= 1000,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] + c) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
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
fn scale_copy(src: &[i32], dst: &mut [i32], n: i32, c: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (-10000 <= #[trigger] src@[(k) as int] <= 10000) as int != 0,
        -100 <= c <= 100,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] * c) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] * c) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = src[i as usize] * c;
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn partition(a: &mut [i32], n: i32, pivot: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] < pivot) as int != 0,
        forall|k: int| (result <= k < n) as int != 0 ==> (a@[(k) as int] >= pivot) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (a)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] < pivot) as int != 0,
            forall|k: int| (j <= k < i) as int != 0 ==> (a@[(k) as int] >= pivot) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn segregate_greater(a: &mut [i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] > val) as int != 0,
        forall|k: int| (result <= k < n) as int != 0 ==> (a@[(k) as int] <= val) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (a)@.len() >= n - 1 + 1, // added: precontion transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] > val) as int != 0,
            forall|k: int| (j <= k < i) as int != 0 ==> (a@[(k) as int] <= val) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn segregate_negative(a: &mut [i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] < 0) as int != 0,
        forall|k: int| (result <= k < n) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (a)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] < 0) as int != 0,
            forall|k: int| (j <= k < i) as int != 0 ==> (a@[(k) as int] >= 0) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn segregate_zeros(a: &mut [i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] == 0) as int != 0,
        forall|k: int| (result <= k < n) as int != 0 ==> (a@[(k) as int] != 0) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (a)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] == 0) as int != 0,
            forall|k: int| (j <= k < i) as int != 0 ==> (a@[(k) as int] != 0) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn partition_le(a: &mut [i32], n: i32, pivot: i32) -> (result: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (a@[(k) as int] <= pivot) as int != 0,
        forall|k: int| (result <= k < n) as int != 0 ==> (a@[(k) as int] > pivot) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (a)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (a@[(k) as int] <= pivot) as int != 0,
            forall|k: int| (j <= k < i) as int != 0 ==> (a@[(k) as int] > pivot) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pointwise_max(a: &[i32], b: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] >= b@[(k) as int]) as int != 0 ==> (
            dst@[(k) as int] == a@[(k) as int]) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] < b@[(k) as int]) as int != 0 ==> (dst@[(
            k) as int] == b@[(k) as int]) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] >= b@[(k) as int]) as int != 0 ==> (
                dst@[(k) as int] == a@[(k) as int]) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] < b@[(k) as int]) as int != 0 ==> (
                dst@[(k) as int] == b@[(k) as int]) as int != 0)) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = if a[i as usize] >= b[i as usize] {
            a[i as usize]
        } else {
            b[i as usize]
        };
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pointwise_min(a: &[i32], b: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] <= b@[(k) as int]) as int != 0 ==> (
            dst@[(k) as int] == a@[(k) as int]) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] > b@[(k) as int]) as int != 0 ==> (dst@[(
            k) as int] == b@[(k) as int]) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] <= b@[(k) as int]) as int != 0 ==> (
                dst@[(k) as int] == a@[(k) as int]) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] > b@[(k) as int]) as int != 0 ==> (
                dst@[(k) as int] == b@[(k) as int]) as int != 0)) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = if a[i as usize] <= b[i as usize] {
            a[i as usize]
        } else {
            b[i as usize]
        };
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn threshold_filter(src: &[i32], dst: &mut [i32], n: i32, threshold: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] >= threshold) as int != 0 ==> (dst@[(
            k) as int] == 1) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] < threshold) as int != 0 ==> (dst@[(
            k) as int] == 0) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] >= threshold) as int != 0 ==> (
                dst@[(k) as int] == 1) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] < threshold) as int != 0 ==> (
                dst@[(k) as int] == 0) as int != 0)) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = if src[i as usize] >= threshold {
            1
        } else {
            0
        };
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn map_square(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (-46340 <= #[trigger] src@[(k) as int] <= 46340) as int != 0,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] * src@[(
            k) as int]) as int != 0,
        forall|k: int| (0 <= k < n) as int != 0 ==> (dst@[(k) as int] >= 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] * src@[(
                k) as int]) as int != 0,
            forall|k: int| (0 <= k < i) as int != 0 ==> (dst@[(k) as int] >= 0) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = src[i as usize] * src[i as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sign_array(a: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] > 0) as int != 0 ==> (dst@[(k) as int]
                == 1) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] == 0) as int != 0 ==> (dst@[(k) as int]
                == 0) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] < 0) as int != 0 ==> (dst@[(k) as int]
                == -1) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] > 0) as int != 0 ==> (dst@[(
                k) as int] == 1) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] == 0) as int != 0 ==> (dst@[(
                k) as int] == 0) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] < 0) as int != 0 ==> (dst@[(
                k) as int] == -1) as int != 0)) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn relu(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] >= 0) as int != 0 ==> (dst@[(k) as int]
                == src@[(k) as int]) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((src@[(k) as int] < 0) as int != 0 ==> (dst@[(k) as int]
                == 0) as int != 0)) as int != 0,
        forall|k: int| (0 <= k < n) as int != 0 ==> (dst@[(k) as int] >= 0) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] >= 0) as int != 0 ==> (dst@[(
                k) as int] == src@[(k) as int]) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((src@[(k) as int] < 0) as int != 0 ==> (dst@[(
                k) as int] == 0) as int != 0)) as int != 0,
            forall|k: int| (0 <= k < i) as int != 0 ==> (dst@[(k) as int] >= 0) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = if src[i as usize] >= 0 {
            src[i as usize]
        } else {
            0
        };
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn masked_copy(src: &[i32], mask: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        mask@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((mask@[(k) as int] != 0) as int != 0 ==> (dst@[(
            k) as int] == src@[(k) as int]) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((mask@[(k) as int] == 0) as int != 0 ==> (dst@[(
            k) as int] == 0) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((mask@[(k) as int] != 0) as int != 0 ==> (dst@[(
                k) as int] == src@[(k) as int]) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((mask@[(k) as int] == 0) as int != 0 ==> (dst@[(
                k) as int] == 0) as int != 0)) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = if mask[i as usize] != 0 {
            src[i as usize]
        } else {
            0
        };
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn compact_positives(src: &[i32], dst: &mut [i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (dst@[(k) as int] > 0) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (dst@[(k) as int] > 0) as int != 0,
        decreases n - i,
    {
        if src[i as usize] > 0 {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn compact_nonzero(src: &[i32], dst: &mut [i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (dst@[(k) as int] != 0) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (dst@[(k) as int] != 0) as int != 0,
        decreases n - i,
    {
        if src[i as usize] != 0 {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn compact_greater(src: &[i32], dst: &mut [i32], n: i32, val: i32) -> (result: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (dst@[(k) as int] > val) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (dst@[(k) as int] > val) as int != 0,
        decreases n - i,
    {
        if src[i as usize] > val {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn compact_in_range(src: &[i32], dst: &mut [i32], n: i32, lo: i32, hi: i32) -> (result: i32)
    requires
        n >= 0,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        0 <= result <= n,
        forall|k: int| (0 <= k < result) as int != 0 ==> (lo <= #[trigger] dst@[(k) as int] <= hi) as int != 0,
{
    let mut j: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= j <= i,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < j) as int != 0 ==> (lo <= #[trigger] dst@[(k) as int] <= hi) as int != 0,
        decreases n - i,
    {
        if src[i as usize] >= lo && src[i as usize] <= hi {
            dst[j as usize] = src[i as usize];
            j += 1;
        }
        i += 1;
    }
    j
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_distinct_sorted(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        (sorted(a, 0 as int, n as int)),
    ensures
        0 <= result <= n,
{
    if n == 0 {
        return 0;
    }
    let mut cnt: i32 = 1;
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            1 <= cnt <= i,
        decreases n - i,
    {
        if a[i as usize] != a[(i - 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn hamming_distance(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
    ensures
        result >= 0,
        result <= n,
{
    let mut d: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= d <= i,
        decreases n - i,
    {
        if a[i as usize] != b[i as usize] {
            d += 1;
        }
        i += 1;
    }
    d
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn longest_plateau(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        result >= 0,
        result <= n,
{
    if n == 0 {
        return 0;
    }
    let mut best: i32 = 1;
    let mut run: i32 = 1;
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            1 <= run <= i,
            1 <= best <= i,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_local_maxima(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
{
    if n <= 2 {
        return 0;
    }
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1,
            0 <= cnt <= i,
        decreases n - 1 - i,
    {
        if a[i as usize] > a[(i - 1) as usize] && a[i as usize] > a[(i + 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_local_minima(a: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
{
    if n <= 2 {
        return 0;
    }
    let mut cnt: i32 = 0;
    let mut i: i32 = 1;
    while i < n - 1
        invariant
            1 <= i <= n - 1,
            0 <= cnt <= i,
        decreases n - 1 - i,
    {
        if a[i as usize] < a[(i - 1) as usize] && a[i as usize] < a[(i + 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }
    cnt
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pointwise_le(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
    ensures
        result == 0 || result == 1,
        (result == 1) as int != 0 ==> (forall|k: int|
            (0 <= k < n) as int != 0 ==> (a@[(k) as int] <= b@[(k) as int]) as int != 0) as int
            != 0,
        (result == 0) as int != 0 ==> (exists|k: int|
            0 <= k < n && a@[(k) as int] > b@[(k) as int]) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= b@[(k) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] > b[i as usize] {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn classify_range(a: &[i32], dst: &mut [i32], n: i32, lo: i32, hi: i32)
    requires
        n >= 0,
        a@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] > hi && a@[(k) as int] >= lo) as int != 0
                ==> (dst@[(k) as int] == 2) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((a@[(k) as int] < lo) as int != 0 ==> (dst@[(k) as int]
                == 0) as int != 0)) as int != 0,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (((lo <= a@[(k) as int] && a@[(k) as int] <= hi) as int
                != 0 ==> (dst@[(k) as int] == 1) as int != 0)) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] > hi && a@[(k) as int] >= lo) as int
                    != 0 ==> (dst@[(k) as int] == 2) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((a@[(k) as int] < lo) as int != 0 ==> (dst@[(
                k) as int] == 0) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (((lo <= a@[(k) as int] && a@[(k) as int] <= hi) as int
                    != 0 ==> (dst@[(k) as int] == 1) as int != 0)) as int != 0,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> ((((dst@[(k) as int] == 0) as int != 0 ==> (a@[(
                k) as int] < lo) as int != 0) && ((dst@[(k) as int] == 1) as int != 0 ==> (lo
                    <= a@[(k) as int] <= hi) as int != 0) && ((dst@[(k) as int] == 2) as int != 0
                    ==> (a@[(k) as int] > hi) as int != 0))) as int != 0,
        decreases n - i,
    {
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn argmax(a: &[i32], n: i32) -> (result: i32)
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
fn argmin(a: &[i32], n: i32) -> (result: i32)
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
fn adjacent_difference(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 1,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n) as int != 0 ==> (-1000000 <= #[trigger] src@[(k) as int] <= 1000000) as int != 0,
    ensures
        dst@[(0) as int] == src@[(0) as int],
        forall|k: int|
            (1 <= k < n) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] - src@[(k
                - 1) as int]) as int != 0,
{
    dst[0] = src[0];
    let mut i: i32 = 1;
    while i < n
        invariant
            1 <= i <= n,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            dst@[(0) as int] == src@[(0) as int],
            forall|k: int|
                (1 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] - src@[(k
                    - 1) as int]) as int != 0,
        decreases n - i,
    {
        dst[i as usize] = src[i as usize] - src[(i - 1) as usize];
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fill_countdown(a: &mut [i32], n: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
        n <= 1000000,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] == n - 1 - k) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (a)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] == n - 1 - k) as int != 0,
        decreases n - i,
    {
        a[i as usize] = n - 1 - i;
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn adjacent_sum_copy(src: &[i32], dst: &mut [i32], n: i32)
    requires
        n >= 1,
        src@.len() >= n - 1 + 1,
        old(dst)@.len() >= n - 1 + 1,
        true,
        forall|k: int|
            (0 <= k < n - 1) as int != 0 ==> (-1000000 <= #[trigger] src@[(k) as int] + src@[(k + 1) as int]
                <= 1000000) as int != 0,
    ensures
        forall|k: int|
            (0 <= k < n - 1) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] + src@[(k
                + 1) as int]) as int != 0,
        dst@[(n - 1) as int] == src@[(n - 1) as int],
{
    let mut i: i32 = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            (dst)@.len() >= n - 1 + 1, // added: precondition transition
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (dst@[(k) as int] == src@[(k) as int] + src@[(k
                    + 1) as int]) as int != 0,
        decreases n - 1 - i,
    {
        dst[i as usize] = src[i as usize] + src[(i + 1) as usize];
        i += 1;
    }
    dst[(n - 1) as usize] = src[(n - 1) as usize];
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn cap_at(a: &mut [i32], n: i32, cap: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] <= cap) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (a)@.len() >= n - 1 + 1, // added: precondition transition 
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] <= cap) as int != 0,
        decreases n - i,
    {
        if a[i as usize] > cap {
            a[i as usize] = cap;
        }
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn floor_at(a: &mut [i32], n: i32, floor_val: i32)
    requires
        n >= 0,
        old(a)@.len() >= n - 1 + 1,
    ensures
        forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] >= floor_val) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (a)@.len() >= n - 1 + 1, // added
            forall|k: int| (0 <= k < i) as int != 0 ==> (a@[(k) as int] >= floor_val) as int != 0,
        decreases n - i,
    {
        if a[i as usize] < floor_val {
            a[i as usize] = floor_val;
        }
        i += 1;
    }
}

fn main() {
}

} // verus!

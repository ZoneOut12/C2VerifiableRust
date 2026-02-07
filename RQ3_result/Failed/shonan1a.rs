#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mult2_bool(m: &[i32], v: &[i32], o: &mut [i32])
    requires
        m@.len() >= 3 + 1,
        v@.len() >= 1 + 1,
        old(o)@.len() >= 1 + 1,
        forall|i: i32| forall|j: i32| (0 <= i < 4 && 0 <= j < 2) as int != 0 ==> (true) as int != 0,
        forall|i: i32| forall|j: i32| (0 <= i < 2 && 0 <= j < 2) as int != 0 ==> (true) as int != 0,
    ensures
        o@[(0) as int] == (m@[(0) as int] && v@[(0) as int]) || (m@[(1) as int] && v@[(1) as int]),
        o@[(1) as int] == (m@[(2) as int] && v@[(0) as int]) || (m@[(3) as int] && v@[(1) as int]),
{
    o[0] = ((m[0] != 0) && (v[0] != 0) || (m[1] != 0) && (v[1] != 0)) as i32;
    o[1] = ((m[2] != 0) && (v[0] != 0) || (m[3] != 0) && (v[1] != 0)) as i32;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mult2(m: &[i32], v: &[i32], o: &mut [i32])
    requires
        m@.len() >= 3 + 1,
        v@.len() >= 1 + 1,
        old(o)@.len() >= 1 + 1,
        forall|i: i32| forall|j: i32| (0 <= i < 4 && 0 <= j < 2) as int != 0 ==> (true) as int != 0,
        forall|i: i32| forall|j: i32| (0 <= i < 2 && 0 <= j < 2) as int != 0 ==> (true) as int != 0,
        forall|i: i32| (0 <= i < 4) as int != 0 ==> (0 <= m@[(i) as int] <= 1) as int != 0,
        forall|i: i32| (0 <= i < 2) as int != 0 ==> (0 <= v@[(i) as int] <= 1) as int != 0,
    ensures
        o@[(0) as int] == m@[(0) as int] * v@[(0) as int] + m@[(1) as int] * v@[(1) as int],
        o@[(1) as int] == m@[(2) as int] * v@[(0) as int] + m@[(3) as int] * v@[(1) as int],
{
    o[0] = m[0] * v[0] + m[1] * v[1];
    o[1] = m[2] * v[0] + m[3] * v[1];
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mult2r_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
    requires
        n == 2,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
        forall|i: i32|
            forall|j: i32| (0 <= i < n * n && 0 <= j < n) as int != 0 ==> (true) as int != 0,
        forall|i: i32| forall|j: i32| (0 <= i < n && 0 <= j < n) as int != 0 ==> (true) as int != 0,
    ensures
        forall|i: i32|
            (0 <= i < n) as int != 0 ==> (o@[(i) as int] == (m@[(n * i + 0) as int] && v@[(
            0) as int]) || (m@[(n * i + 1) as int] && v@[(1) as int])) as int != 0,
{
    let mut r: i32 = 0;
    while r < n
        invariant
            0 <= r <= n,
            forall|i: i32|
                (0 <= i < r) as int != 0 ==> (o@[(i) as int] == (m@[(n * i + 0) as int] && v@[(
                0) as int]) || (m@[(n * i + 1) as int] && v@[(1) as int])) as int != 0,
        decreases n - r,
    {
        let mut t: bool = false;
        let mut c: i32 = 0;
        while c < n
            invariant
                0 <= c <= n,
                t == (if (c == 0) {
                    0
                } else {
                    ((m@[(n * r + 0) as int] && v@[(0) as int]) || (if (c == 1) {
                        0
                    } else {
                        (m@[(n * r + 1) as int] && v@[(1) as int])
                    }))
                }),
            decreases n - c,
        {
            t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
            c += 1;
        }
        o[r as usize] = t as i32;
        r += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mult2s_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
    requires
        n == 2,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
        forall|i: i32|
            forall|j: i32| (0 <= i < n * n && 0 <= j < n) as int != 0 ==> (true) as int != 0,
        forall|i: i32| forall|j: i32| (0 <= i < n && 0 <= j < n) as int != 0 ==> (true) as int != 0,
        m@[(0) as int] == 1,
        m@[(1) as int] == 1,
        m@[(2) as int] == 0,
        m@[(3) as int] == 0,
    ensures
        forall|i: i32|
            (0 <= i < n) as int != 0 ==> (o@[(i) as int] == (m@[(n * i + 0) as int] && v@[(
            0) as int]) || (m@[(n * i + 1) as int] && v@[(1) as int])) as int != 0,
{
    let mut r: i32 = 0;
    let mut t: bool = false;
    let mut c: i32 = 0;
    while c < n
        invariant
            0 <= c <= n,
            t == (if (c == 0) {
                0
            } else {
                ((m@[(n * r + 0) as int] && v@[(0) as int]) || (if (c == 1) {
                    0
                } else {
                    (m@[(n * r + 1) as int] && v@[(1) as int])
                }))
            }),
        decreases n - c,
    {
        t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
        c += 1;
    }
    o[r as usize] = t as i32;
    o[1] = 0;
}

fn main() {
}

} // verus!

#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn row_col_bool(c: int, r: i32, n: i32, m: &[i32], v: &[i32]) -> bool {
    if (0 < c <= n) {
        (((row_col_bool(c - 1 as int, r as i32, n as i32, m, v))) || (m@[(n * r + (c - 1)) as int]
            && v@[((c - 1)) as int]))
    } else {
        0
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mult_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
    requires
        n > 0,
        n < 3,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
        true,
    ensures
        forall|i: i32|
            (0 <= i < n) as int != 0 ==> (o@[(i) as int] == (row_col_bool(
                n as int,
                i as i32,
                n as i32,
                m,
                v,
            ))) as int != 0,
{
    let mut r: i32 = 0;
    while r < n
        invariant
            0 <= r <= n,
            forall|i: i32|
                (0 <= i < r) as int != 0 ==> (o@[(i) as int] == (row_col_bool(
                    n as int,
                    i as i32,
                    n as i32,
                    m,
                    v,
                ))) as int != 0,
        decreases n - r,
    {
        o[r as usize] = 0;
        let mut c: i32 = 0;
        while c < n
            invariant
                0 <= c <= n,
                0 <= r < n,
                forall|i: i32|
                    (0 <= i < r) as int != 0 ==> (o@[(i) as int] == (row_col_bool(
                        n as int,
                        i as i32,
                        n as i32,
                        m,
                        v,
                    ))) as int != 0,
                o@[(r) as int] == (row_col_bool(c as int, r as i32, n as i32, m, v)),
            decreases n - c,
        {
            o[r as usize] = ((o[r as usize] != 0) || (m[(n * r + c) as usize] != 0 && v[c as usize]
                != 0)) as i32;
            c += 1;
        }
        r += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mults_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
    requires
        n > 0,
        n == 2,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
        true,
        m@[(0) as int] == 1,
        m@[(1) as int] == 1,
        m@[(2) as int] == 0,
        m@[(3) as int] == 0,
    ensures
        forall|i: i32|
            (0 <= i < n) as int != 0 ==> (o@[(i) as int] == (row_col_bool(
                n as int,
                i as i32,
                n as i32,
                m,
                v,
            ))) as int != 0,
{
    let r: i32 = 0;
    o[r as usize] = 0;
    let mut c: i32 = 0;
    while c < n
        invariant
            0 <= c <= n,
            0 <= r < n,
            forall|i: i32|
                (0 <= i < r) as int != 0 ==> (o@[(i) as int] == (row_col_bool(
                    n as int,
                    i as i32,
                    n as i32,
                    m,
                    v,
                ))) as int != 0,
            o@[(r) as int] == (row_col_bool(c as int, r as i32, n as i32, m, v)),
        decreases n - c,
    {
        o[r as usize] = ((o[r as usize] != 0) || (m[(n * r + c) as usize] != 0 && v[c as usize]
            != 0)) as i32;
        c += 1;
    }
    o[1] = 0;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_multu_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
    requires
        n > 0,
        n == 2,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
        true,
        m@[(0) as int] == 1,
        m@[(1) as int] == 1,
        m@[(2) as int] == 0,
        m@[(3) as int] == 0,
    ensures
        forall|i: i32|
            (0 <= i < n) as int != 0 ==> (o@[(i) as int] == (row_col_bool(
                n as int,
                i as i32,
                n as i32,
                m,
                v,
            ))) as int != 0,
{
    o[0] = 0;
    o[0] = ((o[0] != 0) || (v[0] != 0)) as i32;
    o[0] = ((o[0] != 0) || (v[1] != 0)) as i32;
    o[1] = 0;
}

fn main() {
}

} // verus!

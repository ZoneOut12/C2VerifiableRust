#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

spec fn ge_zero(x: i32) -> bool{//2A
    0 <= x //2A
} //2A

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mv_mult2_bool(m: &[i32], v: &[i32], o: &mut [i32])
    requires
        m@.len() >= 3 + 1,
        v@.len() >= 1 + 1,
        old(o)@.len() >= 1 + 1,
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 4 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 2 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
    ensures
        o@[(0) as int] != 0 == (m@[(0) as int] != 0 && v@[(0) as int] != 0) || (m@[(1) as int]  != 0&& v@[(1) as int] != 0), //1
        o@[(1) as int] != 0 == (m@[(2) as int] != 0 && v@[(0) as int] != 0) || (m@[(3) as int]  != 0 && v@[(1) as int] != 0), //1
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
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 4 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 2 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
        forall|i: i32| 0 <= i < 4 ==> 0 <= #[trigger] m@[(i) as int] <= 1,//2B
        forall|i: i32| 0 <= i < 2 ==> 0 <= #[trigger] v@[(i) as int] <= 1,//2B
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
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n * n && #[trigger] ge_zero(j) && j < n ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n && #[trigger] ge_zero(j) && j < n ==> true,//2B
    ensures
        forall|i: i32|
            0 <= i < n ==> o@[(i) as int] != 0 == (m@[(n * i + 0) as int]  != 0&& v@[(0) as int] != 0) || (m@[(n//1
                * i + 1) as int]  != 0&& v@[(1) as int] != 0),//1
{
    let mut r: i32 = 0;
    while r < n
        invariant
            (o)@.len() >= n - 1 + 1, //2C
            0 <= r <= n,
            forall|i: i32|
                0 <= i < r ==> o@[(i) as int] != 0 == (m@[(n * i + 0) as int] != 0 && v@[(0) as int] != 0)  || (m@[(//1
                n * i + 1) as int]  != 0&& v@[(1) as int] != 0),//1
        decreases n - r,
    {
        let mut t: bool = false;
        let mut c: i32 = 0;
        while c < n
            invariant
                (o)@.len() >= n - 1 + 1, //2C
                0 <= c <= n,
                t == (if (c == 0) {
                    0 != 0 //1
                } else {
                    ((m@[(n * r + 0) as int] != 0&& v@[(0) as int] != 0) || (if (c == 1) { //1
                        0 != 0 //1
                    } else {
                        (m@[(n * r + 1) as int] != 0&& v@[(1) as int] != 0) //1
                    }))
                }),
                forall|i: i32| 0 <= i < r ==> o@[(i) as int] != 0 == (m@[(n * i + 0) as int] != 0 && v@[(0) as int] != 0)  || (m@[(n * i + 1) as int]  != 0&& v@[(1) as int] != 0),//2A
            decreases n - c,
        {
            t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
            c += 1;
        }
        o[r as usize] = t as i32;
        r += 1;
        assert forall|i: i32| 0 <= i < r implies o@[(i) as int] != 0 == (m@[(n * i + 0) as int] != 0 && v@[(0) as int] != 0)  || (m@[(n * i + 1) as int]  != 0&& v@[(1) as int] != 0) by{ //2A
            assert((o[(r-1) as int] != 0) == (m@[(n * (r - 1) + 0) as int] != 0 && v@[(0) as int] != 0)  || (m@[(n * (r-1) + 1) as int]  != 0 && v@[(1) as int] != 0));//2A
        } //2A
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
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n * n && #[trigger] ge_zero(j) && j < n ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n && #[trigger] ge_zero(j) && j < n ==> true,//2B
        m@[(0) as int] == 1,
        m@[(1) as int] == 1,
        m@[(2) as int] == 0,
        m@[(3) as int] == 0,
    ensures
        forall|i: i32|
            0 <= i < n ==> o@[(i) as int]  != 0== (m@[(n * i + 0) as int]  != 0&& v@[(0) as int] != 0) || (m@[(n //1
                * i + 1) as int]  != 0&& v@[(1) as int] != 0),//1
{
    let mut r: i32 = 0;
    let mut t: bool = false;
    let mut c: i32 = 0;
    while c < n
        invariant
            (o)@.len() >= n - 1 + 1, //2C
            0 <= c <= n,
            t == (if (c == 0) {
                0 != 0 //1
            } else {
                ((m@[(n * r + 0) as int] != 0&& v@[(0) as int]!= 0) || (if (c == 1) { //1
                    0 != 0 //1
                } else {
                    (m@[(n * r + 1) as int]!= 0 && v@[(1) as int]!= 0) //1
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

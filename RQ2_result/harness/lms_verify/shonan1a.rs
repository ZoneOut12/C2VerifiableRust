#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

spec fn ge_zero(x: i32) -> bool{//2A
    0 <= x //2A
} //2A

fn CheckPre_mv_mult2_bool(m: &[i32], v: &[i32], old_o: &[i32])
    requires
        m@.len() >= 3 + 1,
        v@.len() >= 1 + 1,
        old_o@.len() >= 1 + 1,
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 4 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 2 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
{}


fn CheckPost_mv_mult2_bool(m: &[i32], v: &[i32], o: &[i32])
    requires
        o@[(0) as int] != 0 == (m@[(0) as int] != 0 && v@[(0) as int] != 0) || (m@[(1) as int]  != 0&& v@[(1) as int] != 0), //1
        o@[(1) as int] != 0 == (m@[(2) as int] != 0 && v@[(0) as int] != 0) || (m@[(3) as int]  != 0 && v@[(1) as int] != 0), //1
{}

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

fn CheckPre_mv_mult2(m: &[i32], v: &[i32], old_o: &[i32])
    requires
        m@.len() >= 3 + 1,
        v@.len() >= 1 + 1,
        old_o@.len() >= 1 + 1,
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 4 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < 2 && #[trigger] ge_zero(j) && j < 2 ==> true,//2B
        forall|i: i32| 0 <= i < 4 ==> 0 <= #[trigger] m@[(i) as int] <= 1,//2B
        forall|i: i32| 0 <= i < 2 ==> 0 <= #[trigger] v@[(i) as int] <= 1,//2B
{}

fn CheckPost_mv_mult2(m: &[i32], v: &[i32], o: &[i32])
    requires  
        o@[(0) as int] == m@[(0) as int] * v@[(0) as int] + m@[(1) as int] * v@[(1) as int],
        o@[(1) as int] == m@[(2) as int] * v@[(0) as int] + m@[(3) as int] * v@[(1) as int],
{}

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

fn CheckPre_mv_mult2r_bool(n: i32, m: &[i32], v: &[i32], old_o: &[i32])
    requires
        n == 2,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old_o@.len() >= n - 1 + 1,
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n * n && #[trigger] ge_zero(j) && j < n ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n && #[trigger] ge_zero(j) && j < n ==> true,//2B
{}

fn CheckPost_mv_mult2r_bool(n: i32, m: &[i32], v: &[i32], o: &[i32])
    requires
        forall|i: i32|
            0 <= i < n ==> o@[(i) as int] != 0 == (m@[(n * i + 0) as int]  != 0&& v@[(0) as int] != 0) || (m@[(n//1
                * i + 1) as int]  != 0&& v@[(1) as int] != 0),//1
{}

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

fn CheckPre_mv_mult2s_bool(n: i32, m: &[i32], v: &[i32], old_o: &[i32])
    requires
        n == 2,
        m@.len() >= n * n - 1 + 1,
        v@.len() >= n - 1 + 1,
        old_o@.len() >= n - 1 + 1,
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n * n && #[trigger] ge_zero(j) && j < n ==> true,//2B
        forall|i: i32| forall|j: i32| #[trigger] ge_zero(i) && i < n && #[trigger] ge_zero(j) && j < n ==> true,//2B
        m@[(0) as int] == 1,
        m@[(1) as int] == 1,
        m@[(2) as int] == 0,
        m@[(3) as int] == 0,
{}

fn CheckPost_mv_mult2s_bool(n: i32, m: &[i32], v: &[i32], o: &[i32])
    requires
        forall|i: i32|
            0 <= i < n ==> o@[(i) as int]  != 0== (m@[(n * i + 0) as int]  != 0&& v@[(0) as int] != 0) || (m@[(n //1
                * i + 1) as int]  != 0&& v@[(1) as int] != 0),//1
{}

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

fn valid_test_harness_mv_mult2_bool() {
    // Case 1: Identity Matrix
    let m1 = [1, 0, 0, 1]; let v1 = [1, 1]; let mut o1 = [0; 2];
    CheckPre_mv_mult2_bool(&m1, &v1, &o1);
    let result1 = [1, 1];
    CheckPost_mv_mult2_bool(&m1, &v1, &result1);

    // Case 2: All zeros matrix
    let m2 = [0, 0, 0, 0]; let v2 = [1, 1]; let mut o2 = [0; 2];
    CheckPre_mv_mult2_bool(&m2, &v2, &o2);
    let result2 = [0, 0];
    CheckPost_mv_mult2_bool(&m2, &v2, &result2);

    // Case 3: All ones matrix
    let m3 = [1, 1, 1, 1]; let v3 = [1, 1]; let mut o3 = [0; 2];
    CheckPre_mv_mult2_bool(&m3, &v3, &o3);
    let result3 = [1, 1];
    CheckPost_mv_mult2_bool(&m3, &v3, &result3);

    // Case 4: Zero vector
    let m4 = [1, 1, 1, 1]; let v4 = [0, 0]; let mut o4 = [0; 2];
    CheckPre_mv_mult2_bool(&m4, &v4, &o4);
    let result4 = [0, 0];
    CheckPost_mv_mult2_bool(&m4, &v4, &result4);

    // Case 5: Top row active
    let m5 = [1, 1, 0, 0]; let v5 = [1, 0]; let mut o5 = [0; 2];
    CheckPre_mv_mult2_bool(&m5, &v5, &o5);
    let result5 = [1, 0];
    CheckPost_mv_mult2_bool(&m5, &v5, &result5);

    // Case 6: Sparse activation
    let m6 = [0, 1, 1, 0]; let v6 = [0, 1]; let mut o6 = [0; 2];
    CheckPre_mv_mult2_bool(&m6, &v6, &o6);
    let result6 = [1, 0];
    CheckPost_mv_mult2_bool(&m6, &v6, &result6);

    // Case 7: Permutation-like
    let m7 = [0, 1, 1, 0]; let v7 = [1, 0]; let mut o7 = [0; 2];
    CheckPre_mv_mult2_bool(&m7, &v7, &o7);
    let result7 = [0, 1];
    CheckPost_mv_mult2_bool(&m7, &v7, &result7);
}

fn valid_test_harness_mv_mult2() {
    // Case 1: Identity
    let m1 = [1, 0, 0, 1]; let v1 = [1, 1]; let mut o1 = [0; 2];
    CheckPre_mv_mult2(&m1, &v1, &o1);
    let result1 = [1, 1];
    CheckPost_mv_mult2(&m1, &v1, &result1);

    // Case 2: Arithmetic Sum (1*1 + 1*1 = 2)
    let m2 = [1, 1, 1, 1]; let v2 = [1, 1]; let mut o2 = [0; 2];
    CheckPre_mv_mult2(&m2, &v2, &o2);
    let result2 = [2, 2];
    CheckPost_mv_mult2(&m2, &v2, &result2);

    // Case 3: Mixed binary
    let m3 = [1, 1, 0, 0]; let v3 = [1, 1]; let mut o3 = [0; 2];
    CheckPre_mv_mult2(&m3, &v3, &o3);
    let result3 = [2, 0];
    CheckPost_mv_mult2(&m3, &v3, &result3);

    // Case 4: Row 2 activation
    let m4 = [0, 0, 1, 1]; let v4 = [1, 1]; let mut o4 = [0; 2];
    CheckPre_mv_mult2(&m4, &v4, &o4);
    let result4 = [0, 2];
    CheckPost_mv_mult2(&m4, &v4, &result4);

    // Case 5: Sparse
    let m5 = [1, 0, 1, 0]; let v5 = [1, 0]; let mut o5 = [0; 2];
    CheckPre_mv_mult2(&m5, &v5, &o5);
    let result5 = [1, 1];
    CheckPost_mv_mult2(&m5, &v5, &result5);

    // Case 6: Zero Vector
    let m6 = [1, 1, 1, 1]; let v6 = [0, 0]; let mut o6 = [0; 2];
    CheckPre_mv_mult2(&m6, &v6, &o6);
    let result6 = [0, 0];
    CheckPost_mv_mult2(&m6, &v6, &result6);

    // Case 7: All zeros
    let m7 = [0, 0, 0, 0]; let v7 = [1, 1]; let mut o7 = [0; 2];
    CheckPre_mv_mult2(&m7, &v7, &o7);
    let result7 = [0, 0];
    CheckPost_mv_mult2(&m7, &v7, &result7);
}

fn valid_test_harness_mv_mult2r_bool() {
    let mut o = [0; 2];

    // Case 1: Identity Matrix
    let m1 = [1, 0, 0, 1]; let v1 = [1, 1];
    CheckPre_mv_mult2r_bool(2, &m1, &v1, &o);
    let res1 = [1, 1];
    CheckPost_mv_mult2r_bool(2, &m1, &v1, &res1);

    // Case 2: All zeros matrix
    let m2 = [0, 0, 0, 0]; let v2 = [1, 1];
    CheckPre_mv_mult2r_bool(2, &m2, &v2, &o);
    let res2 = [0, 0];
    CheckPost_mv_mult2r_bool(2, &m2, &v2, &res2);

    // Case 3: All ones matrix
    let m3 = [1, 1, 1, 1]; let v3 = [1, 1];
    CheckPre_mv_mult2r_bool(2, &m3, &v3, &o);
    let res3 = [1, 1];
    CheckPost_mv_mult2r_bool(2, &m3, &v3, &res3);

    // Case 4: Zero vector
    let m4 = [1, 1, 1, 1]; let v4 = [0, 0];
    CheckPre_mv_mult2r_bool(2, &m4, &v4, &o);
    let res4 = [0, 0];
    CheckPost_mv_mult2r_bool(2, &m4, &v4, &res4);

    // Case 5: Single element activation (Top Left)
    let m5 = [1, 0, 0, 0]; let v5 = [1, 1];
    CheckPre_mv_mult2r_bool(2, &m5, &v5, &o);
    let res5 = [1, 0];
    CheckPost_mv_mult2r_bool(2, &m5, &v5, &res5);

    // Case 6: Sparse Matrix / Sparse Vector
    let m6 = [0, 1, 1, 0]; let v6 = [0, 1];
    CheckPre_mv_mult2r_bool(2, &m6, &v6, &o);
    let res6 = [1, 0];
    CheckPost_mv_mult2r_bool(2, &m6, &v6, &res6);

    // Case 7: Row swap pattern
    let m7 = [0, 1, 1, 0]; let v7 = [1, 0];
    CheckPre_mv_mult2r_bool(2, &m7, &v7, &o);
    let res7 = [0, 1];
    CheckPost_mv_mult2r_bool(2, &m7, &v7, &res7);
}

fn valid_test_harness_mv_mult2s_bool() {
    let ms = [1, 1, 0, 0]; // Specific matrix required by ACSL
    let mut o = [0; 2];

    // Case 1: Full Vector
    let v1 = [1, 1];
    CheckPre_mv_mult2s_bool(2, &ms, &v1, &o);
    let res1 = [1, 0]; 
    CheckPost_mv_mult2s_bool(2, &ms, &v1, &res1);

    // Case 2: Zero Vector
    let v2 = [0, 0];
    CheckPre_mv_mult2s_bool(2, &ms, &v2, &o);
    let res2 = [0, 0];
    CheckPost_mv_mult2s_bool(2, &ms, &v2, &res2);

    // Case 3: First element only
    let v3 = [1, 0];
    CheckPre_mv_mult2s_bool(2, &ms, &v3, &o);
    let res3 = [1, 0];
    CheckPost_mv_mult2s_bool(2, &ms, &v3, &res3);

    // Case 4: Second element only
    let v4 = [0, 1];
    CheckPre_mv_mult2s_bool(2, &ms, &v4, &o);
    let res4 = [1, 0];
    CheckPost_mv_mult2s_bool(2, &ms, &v4, &res4);

    // Case 5: Repeat Full Vector (Verification of consistency)
    let v5 = [1, 1];
    CheckPre_mv_mult2s_bool(2, &ms, &v5, &o);
    let res5 = [1, 0];
    CheckPost_mv_mult2s_bool(2, &ms, &v5, &res5);

    // Case 6: Repeat First element
    let v6 = [1, 0];
    CheckPre_mv_mult2s_bool(2, &ms, &v6, &o);
    let res6 = [1, 0];
    CheckPost_mv_mult2s_bool(2, &ms, &v6, &res6);

    // Case 7: Repeat Second element
    let v7 = [0, 1];
    CheckPre_mv_mult2s_bool(2, &ms, &v7, &o);
    let res7 = [1, 0];
    CheckPost_mv_mult2s_bool(2, &ms, &v7, &res7);
}

fn invalid_test_harness_mv_mult2_bool() {
    let m_ok = [1, 0, 0, 1];
    let v_ok = [1, 1];
    let o_ok = [0, 0];

    // Case 8: Violation of \valid_read - Matrix buffer too short
    let m_invalid = [1, 0, 0]; 
    CheckPre_mv_mult2_bool(&m_invalid, &v_ok, &o_ok); 

    // Case 9: Violation of \valid - Output buffer too short
    // ACSL requires o+(0..1) to be valid. Here we provide only 1 slot.
    let o_short = [0; 1];
    CheckPre_mv_mult2_bool(&m_ok, &v_ok, &o_short); 
}

fn invalid_test_harness_mv_mult2() {
    let v_ok = [1, 1];
    let o_ok = [0, 0];

    let m_bad_val = [2, 0, 0, 1]; 
    CheckPre_mv_mult2(&m_bad_val, &v_ok, &o_ok);

    let m_ok = [1, 1, 1, 1];
    let v_bad_val = [1, -1]; 
    CheckPre_mv_mult2(&m_ok, &v_bad_val, &o_ok);
}

fn invalid_test_harness_mv_mult2r_bool() {
    let m = [1, 0, 0, 1];
    let v = [1, 1];
    let o = [0, 0];

    let n_wrong = 3;
    CheckPre_mv_mult2r_bool(n_wrong, &m, &v, &o);

    let v_short = [1];
    CheckPre_mv_mult2r_bool(2, &m, &v_short, &o);
}

fn invalid_test_harness_mv_mult2s_bool() {
    let v = [1, 1];
    let o = [0, 0];

    let m_wrong_content = [0, 0, 0, 0];
    CheckPre_mv_mult2s_bool(2, &m_wrong_content, &v, &o);

    let m_correct_content = [1, 1, 0, 0];
    CheckPre_mv_mult2s_bool(1, &m_correct_content, &v, &o);
}

} // verus!


// RAC
// fn mv_mult2_bool(m: &[i32], v: &[i32], o: &mut [i32])
// {
//     o[0] = ((m[0] != 0) && (v[0] != 0) || (m[1] != 0) && (v[1] != 0)) as i32;
//     o[1] = ((m[2] != 0) && (v[0] != 0) || (m[3] != 0) && (v[1] != 0)) as i32;
// }

// fn mv_mult2(m: &[i32], v: &[i32], o: &mut [i32])
// {
//     o[0] = m[0] * v[0] + m[1] * v[1];
//     o[1] = m[2] * v[0] + m[3] * v[1];
// }

// fn mv_mult2r_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
// {
//     let mut r: i32 = 0;
//     while r < n
//     {
//         let old_measure = n - r;
//         assert!(
//             (o.len() as i32) >= n - 1 + 1 &&
//             0 <= r && r <= n &&
//             (0..r).all(|i| (o[(i) as usize] != 0) == (m[(n * i + 0) as usize] != 0 && v[(0) as usize] != 0) || (m[(
//                 n * i + 1) as usize]  != 0 && v[1] != 0))
//         );
//         let mut t: bool = false;
//         let mut c: i32 = 0;
//         while c < n
//         {
//             assert!(
//                 (o.len() as i32) >= n - 1 + 1 &&
//                 0 <= c && c <= n &&
//                 t == (if (c == 0) {
//                     0 != 0 //1
//                 } else {
//                     ((m[(n * r + 0) as usize] != 0 && v[0] != 0) || (if (c == 1) { //1
//                         0 != 0 //1
//                     } else {
//                         (m[(n * r + 1) as usize] != 0 && v[1] != 0) //1
//                     }))
//                 })
//             );
//             let old_measure2 = n - c;
//             t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
//             c += 1;
//             assert!(old_measure2 > n - c);
//         }
//         assert!(
//                 (o.len() as i32) >= n - 1 + 1 &&
//                 0 <= c && c <= n &&
//                 t == (if (c == 0) {
//                     0 != 0 //1
//                 } else {
//                     ((m[(n * r + 0) as usize] != 0 && v[0] != 0) || (if (c == 1) { //1
//                         0 != 0 //1
//                     } else {
//                         (m[(n * r + 1) as usize] != 0 && v[1] != 0) //1
//                     }))
//                 })
//             );
//         o[r as usize] = t as i32;
//         r += 1;
//         assert!(old_measure > n - r);
//     }
//     assert!(
//         (o.len() as i32) >= n - 1 + 1 &&
//         0 <= r && r <= n &&
//         (0..r).all(|i| (o[(i) as usize] != 0) == (m[(n * i + 0) as usize] != 0 && v[(0) as usize] != 0) || (m[(
//             n * i + 1) as usize]  != 0 && v[1] != 0))
//     );
// }

// fn mv_mult2s_bool(n: i32, m: &[i32], v: &[i32], o: &mut [i32])
// {
//     let mut r: i32 = 0;
//     let mut t: bool = false;
//     let mut c: i32 = 0;
//     while c < n
//     {
//         assert!(
//             (o.len() as i32) >= n - 1 + 1 &&
//             0 <= c && c <= n &&
//             t == (if (c == 0) {
//                 0 != 0 //1
//             } else {
//                 ((m[(n * r + 0) as usize] != 0&& v[0]!= 0) || (if (c == 1) { //1
//                     0 != 0 //1
//                 } else {
//                     (m[(n * r + 1) as usize]!= 0 && v[1]!= 0) //1
//                 }))
//             }),
//         );
//         let old_measure = n - c;
//         t = t || ((m[(n * r + c) as usize] != 0) && (v[c as usize] != 0));
//         c += 1;
//         assert!(old_measure > n - c);
//     }
//     assert!(
//         (o.len() as i32) >= n - 1 + 1 &&
//         0 <= c && c <= n &&
//         t == (if (c == 0) {
//             0 != 0 //1
//         } else {
//             ((m[(n * r + 0) as usize] != 0&& v[0]!= 0) || (if (c == 1) { //1
//                 0 != 0 //1
//             } else {
//                 (m[(n * r + 1) as usize]!= 0 && v[1]!= 0) //1
//             }))
//         }),
//     );
//     o[r as usize] = t as i32;
//     o[1] = 0;
// }

// fn main() {
//     valid_test_harness_mv_mult2r_bool();
//     valid_test_harness_mv_mult2s_bool();
// }

// fn valid_test_harness_mv_mult2r_bool() {
//     let mut o = [0; 2];

//     // Case 1: Identity Matrix
//     let m1 = [1, 0, 0, 1]; let v1 = [1, 1];
//     mv_mult2r_bool(2, &m1, &v1, &mut o);

//     // Case 2: All zeros matrix
//     let m2 = [0, 0, 0, 0]; let v2 = [1, 1];
//     mv_mult2r_bool(2, &m2, &v2, &mut o);

//     // Case 3: All ones matrix
//     let m3 = [1, 1, 1, 1]; let v3 = [1, 1];
//     mv_mult2r_bool(2, &m3, &v3, &mut o);

//     // Case 4: Zero vector
//     let m4 = [1, 1, 1, 1]; let v4 = [0, 0];
//     mv_mult2r_bool(2, &m4, &v4, &mut o);

//     // Case 5: Single element activation (Top Left)
//     let m5 = [1, 0, 0, 0]; let v5 = [1, 1];
//     mv_mult2r_bool(2, &m5, &v5, &mut o);

//     // Case 6: Sparse Matrix / Sparse Vector
//     let m6 = [0, 1, 1, 0]; let v6 = [0, 1];
//     mv_mult2r_bool(2, &m6, &v6, &mut o);

//     // Case 7: Row swap pattern
//     let m7 = [0, 1, 1, 0]; let v7 = [1, 0];
//     mv_mult2r_bool(2, &m7, &v7, &mut o);
// }

// fn valid_test_harness_mv_mult2s_bool() {
//     let ms = [1, 1, 0, 0]; // Specific matrix required by ACSL
//     let mut o = [0; 2];

//     // Case 1: Full Vector
//     let v1 = [1, 1];
//     mv_mult2s_bool(2, &ms, &v1, &mut o);

//     // Case 2: Zero Vector
//     let v2 = [0, 0];
//     mv_mult2s_bool(2, &ms, &v2, &mut o);

//     // Case 3: First element only
//     let v3 = [1, 0];
//     mv_mult2s_bool(2, &ms, &v3, &mut o);

//     // Case 4: Second element only
//     let v4 = [0, 1];
//     mv_mult2s_bool(2, &ms, &v4, &mut o);

//     // Case 5: Repeat Full Vector (Verification of consistency)
//     let v5 = [1, 1];
//     mv_mult2s_bool(2, &ms, &v5, &mut o);

//     // Case 6: Repeat First element
//     let v6 = [1, 0];
//     mv_mult2s_bool(2, &ms, &v6, &mut o);

//     // Case 7: Repeat Second element
//     let v7 = [0, 1];
//     mv_mult2s_bool(2, &ms, &v7, &mut o);
// }

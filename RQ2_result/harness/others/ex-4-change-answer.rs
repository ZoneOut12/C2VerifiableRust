#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

// #[derive(Copy, Clone)]
// enum note {
//     N500,
//     N200,
//     N100,
//     N50,
//     N20,
//     N10,
//     N5,
//     N2,
//     N1,
// }

mod note{
    pub const N500: i32 = 0;
    pub const N200: i32 = 1;
    pub const N100: i32 = 2;
    pub const N50: i32 = 3;
    pub const N20: i32 = 4;
    pub const N10: i32 = 5;
    pub const N5: i32 = 6;
    pub const N2: i32 = 7;
    pub const N1: i32 = 8;
}

use note::*;

const values: [i32; 9] = [500, 200, 100, 50, 20, 10, 5, 2, 1];

fn CheckPre_remove_max_notes(n: i32, old_rest: &i32)
    requires
        N500 <= n <= N1,
        ((old_rest)@) >= 0,
{}

fn CheckPost_remove_max_notes(old_rest: &i32, n: i32, rest: &i32, result: i32)
    requires
        result == ((old_rest)@) / values@[(n) as int],
        ((old_rest)@) == ((rest)@) + result * values@[(n) as int],
{}


#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn remove_max_notes(n: i32, rest: &mut i32) -> (result: i32)
    requires
        N500 <= n <= N1,
        true && ((old(rest))@) >= 0,
    ensures
        result == ((old(rest))@) / values@[(n) as int],
        ((old(rest))@) == ((rest)@) + result * values@[(n) as int],
{
    let num: i32 = *rest / values[n as usize];
    *rest -= num * values[n as usize];
    num
}

fn CheckPre_make_change(amount: i32, received: i32, old_change: &[i32])
    requires
        old_change@.len() >= 8 + 1,
        amount >= 0 && received >= 0,
{}

fn CheckPost_make_change(amount: i32, received: i32, change: &[i32], result: i32)
    requires
        (amount > received) ==> (result == -1),
        (amount <= received) ==> (result == 0) && (received - amount == change@[(N500) as int]
            * values@[(N500) as int] + change@[(N200) as int] * values@[(N200) as int] + change@[(
        N100) as int] * values@[(N100) as int] + change@[(N50) as int] * values@[(N50) as int]
            + change@[(N20) as int] * values@[(N20) as int] + change@[(N10) as int] * values@[(
        N10) as int] + change@[(N5) as int] * values@[(N5) as int] + change@[(N2) as int]
            * values@[(N2) as int] + change@[(N1) as int] * values@[(N1) as int]) && (change@[(
        N1) as int] * values@[(N1) as int] < values@[(N2) as int] && change@[(N2) as int]
            * values@[(N2) as int] < values@[(N5) as int] && change@[(N5) as int] * values@[(
        N5) as int] < values@[(N10) as int] && change@[(N10) as int] * values@[(N10) as int]
            < values@[(N20) as int] && change@[(N20) as int] * values@[(N20) as int] < values@[(
        N50) as int] && change@[(N50) as int] * values@[(N50) as int] < values@[(N100) as int]
            && change@[(N100) as int] * values@[(N100) as int] < values@[(N200) as int] && change@[(
        N200) as int] * values@[(N200) as int] < values@[(N500) as int])
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn make_change(amount: i32, received: i32, change: &mut [i32]) -> (result: i32)
    requires
        old(change)@.len() >= 8 + 1,
        amount >= 0 && received >= 0,
    ensures
        (amount > received) ==> (result == -1),
        (amount <= received) ==> (result == 0) && (received - amount == change@[(N500) as int]
            * values@[(N500) as int] + change@[(N200) as int] * values@[(N200) as int] + change@[(
        N100) as int] * values@[(N100) as int] + change@[(N50) as int] * values@[(N50) as int]
            + change@[(N20) as int] * values@[(N20) as int] + change@[(N10) as int] * values@[(
        N10) as int] + change@[(N5) as int] * values@[(N5) as int] + change@[(N2) as int]
            * values@[(N2) as int] + change@[(N1) as int] * values@[(N1) as int]) && (change@[(
        N1) as int] * values@[(N1) as int] < values@[(N2) as int] && change@[(N2) as int]
            * values@[(N2) as int] < values@[(N5) as int] && change@[(N5) as int] * values@[(
        N5) as int] < values@[(N10) as int] && change@[(N10) as int] * values@[(N10) as int]
            < values@[(N20) as int] && change@[(N20) as int] * values@[(N20) as int] < values@[(
        N50) as int] && change@[(N50) as int] * values@[(N50) as int] < values@[(N100) as int]
            && change@[(N100) as int] * values@[(N100) as int] < values@[(N200) as int] && change@[(
        N200) as int] * values@[(N200) as int] < values@[(N500) as int]),
{
    if amount > received {
        return -1;
    }
    let mut rest: i32 = received - amount;

    change[N500 as usize] = remove_max_notes(N500, &mut rest);
    change[N200 as usize] = remove_max_notes(N200, &mut rest);
    change[N100 as usize] = remove_max_notes(N100, &mut rest);
    change[N50 as usize] = remove_max_notes(N50, &mut rest);
    change[N20 as usize] = remove_max_notes(N20, &mut rest);
    change[N10 as usize] = remove_max_notes(N10, &mut rest);
    change[N5 as usize] = remove_max_notes(N5, &mut rest);
    change[N2 as usize] = remove_max_notes(N2, &mut rest);
    change[N1 as usize] = remove_max_notes(N1, &mut rest);

    0
}

fn main() {
}

fn valid_test_harness_remove_max_notes() {
    // --- Test Case 1: Standard case - amount is perfectly divisible ---
    let old_rest1 = 1000;
    let mut rest1 = 1000;
    let n1 = note::N500;
    CheckPre_remove_max_notes(n1, &rest1);
    // Simulated execution: 1000 / 500 = 2, remainder 0
    let result1 = 2;
    rest1 = 0;
    CheckPost_remove_max_notes(&old_rest1, n1, &rest1, result1);

    // --- Test Case 2: Standard case - partial removal with remainder ---
    let old_rest2 = 350;
    let mut rest2 = 350;
    let n2 = note::N100;
    CheckPre_remove_max_notes(n2, &rest2);
    // Simulated execution: 350 / 100 = 3, remainder 50
    let result2 = 3;
    rest2 = 50;
    CheckPost_remove_max_notes(&old_rest2, n2, &rest2, result2);

    // --- Test Case 3: Amount is less than the note value ---
    let old_rest3 = 15;
    let mut rest3 = 15;
    let n3 = note::N20;
    CheckPre_remove_max_notes(n3, &rest3);
    // Simulated execution: 15 / 20 = 0, remainder 15
    let result3 = 0;
    rest3 = 15;
    CheckPost_remove_max_notes(&old_rest3, n3, &rest3, result3);

    // --- Test Case 4: Initial amount is exactly zero ---
    let old_rest4 = 0;
    let mut rest4 = 0;
    let n4 = note::N50;
    CheckPre_remove_max_notes(n4, &rest4);
    let result4 = 0;
    rest4 = 0;
    CheckPost_remove_max_notes(&old_rest4, n4, &rest4, result4);

    // --- Test Case 5: Testing smallest denomination ---
    let old_rest5 = 7;
    let mut rest5 = 7;
    let n5 = note::N1;
    CheckPre_remove_max_notes(n5, &rest5);
    let result5 = 7;
    rest5 = 0;
    CheckPost_remove_max_notes(&old_rest5, n5, &rest5, result5);

    // --- Test Case 6: Amount exactly equals note value ---
    let old_rest6 = 200;
    let mut rest6 = 200;
    let n6 = note::N200;
    CheckPre_remove_max_notes(n6, &rest6);
    let result6 = 1;
    rest6 = 0;
    CheckPost_remove_max_notes(&old_rest6, n6, &rest6, result6);

    // --- Test Case 7: Large amount with high-value notes ---
    let old_rest7 = 2300;
    let mut rest7 = 2300;
    let n7 = note::N500;
    CheckPre_remove_max_notes(n7, &rest7);
    let result7 = 4;
    rest7 = 300;
    CheckPost_remove_max_notes(&old_rest7, n7, &rest7, result7);
}

fn valid_test_harness_make_change() {
    // --- Test Case 1: Valid - amount > received ---
    let (amount1, received1) = (150, 100);
    let mut change1 = [0; 9];
    CheckPre_make_change(amount1, received1, &change1);
    let result1 = -1;
    CheckPost_make_change(amount1, received1, &change1, result1);

    // --- Test Case 2: Valid - exact payment ---
    let (amount2, received2) = (50, 50);
    let mut change2 = [0; 9];
    CheckPre_make_change(amount2, received2, &change2);
    let result2 = 0;
    let expected2 = [0, 0, 0, 0, 0, 0, 0, 0, 0];
    CheckPost_make_change(amount2, received2, &expected2, result2);

    // --- Test Case 3: Valid - typical change calculation (177 remaining) ---
    let (amount3, received3) = (323, 500);
    let mut change3 = [0; 9];
    CheckPre_make_change(amount3, received3, &change3);
    let result3 = 0;
    // 177 = 1*100 + 1*50 + 1*20 + 1*5 + 1*2
    let expected3 = [0, 0, 1, 1, 1, 0, 1, 1, 0];
    CheckPost_make_change(amount3, received3, &expected3, result3);

    // --- Test Case 4: Boundary - maximum note ---
    let (amount4, received4) = (0, 500);
    let mut change4 = [0; 9];
    CheckPre_make_change(amount4, received4, &change4);
    let result4 = 0;
    let expected4 = [1, 0, 0, 0, 0, 0, 0, 0, 0];
    CheckPost_make_change(amount4, received4, &expected4, result4);

    // --- Test Case 5: Valid - small change ---
    let (amount5, received5) = (97, 100);
    let mut change5 = [0; 9];
    CheckPre_make_change(amount5, received5, &change5);
    let result5 = 0;
    // 3 = 1*2 + 1*1
    let expected5 = [0, 0, 0, 0, 0, 0, 0, 1, 1];
    CheckPost_make_change(amount5, received5, &expected5, result5);

    // --- Test Case 6: Boundary - change just below highest note ---
    let (amount6, received6) = (499, 500);
    let mut change6 = [0; 9];
    CheckPre_make_change(amount6, received6, &change6);
    let result6 = 0;
    // 1 = 1*1
    let expected6 = [0, 0, 0, 0, 0, 0, 0, 0, 1];
    CheckPost_make_change(amount6, received6, &expected6, result6);

    // --- Test Case 7: Valid (New) - All denominations used ---
    // Change sum: 500+200+100+50+20+10+5+2+1 = 888
    let (amount7, received7) = (0, 888);
    let mut change7 = [0; 9];
    CheckPre_make_change(amount7, received7, &change7);
    let result7 = 0;
    let expected7 = [1, 1, 1, 1, 1, 1, 1, 1, 1];
    CheckPost_make_change(amount7, received7, &expected7, result7);
}

fn invalid_test_harness_make_change() {
    // --- Test Case 8: Invalid - NULL change array ---
    // let (amount8, received8) = (50, 100);
    // CheckPre_make_change(amount8, received8, None);

    // --- Test Case 9: Invalid - negative amount ---
    // Violates: requires amount >= 0
    let (amount9, received9) = (-10, 100);
    let mut change9 = [0; 9];
    CheckPre_make_change(amount9, received9, &change9);
}

fn invalid_test_harness_remove_max_notes() {
    // --- Test Case 8: Violates \valid(rest) ---
    // let n8 = note::N100;
    // CheckPre_remove_max_notes(n8, None);

    // --- Test Case 9: Violates *rest >= 0 ---
    let old_rest9 = -100;
    let rest_neg = -100;
    let n9 = note::N50;
    // This violates: requires *rest >= 0
    CheckPre_remove_max_notes(n9, &rest_neg);
}

} // verus!

#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[derive(Copy, Clone)]
enum note {
    N500,
    N200,
    N100,
    N50,
    N20,
    N10,
    N5,
    N2,
    N1,
}

use note::*;

const values: [i32; 9] = [500, 200, 100, 50, 20, 10, 5, 2, 1];

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn remove_max_notes(n: note, rest: &mut i32) -> (result: i32)
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

} // verus!

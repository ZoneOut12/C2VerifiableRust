#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

spec fn ge_zero(x: i32) -> bool { //2A
    x >= 0 //2A
}//2A

pub open spec fn inv_matrix_Boolean(x26: &[i32], x27: int, x28: int) -> bool {
    (((((x27 < 100) && (x28 < 100)) && (0 < x27)) && (0 < x28)) && (((x27 * x28) > 0) && x26@.len()
        >= (x27 * x28) - 1 + 1))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> (result: i32)
    requires
        ((((((((0 < x0) && (x0 < 100)) && (0 < x1)) && (x1 < 100)) && (0 <= x2)) && (0 <= x3)) && (
        x2 < x0)) && (x3 < x1)),
    ensures
        ((0 <= result) && (result < (x0 * x1))),
{
    let x5: i32 = x2 * x1;
    let x6: i32 = x5 + x3;
    x6
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(
    x63: &[i32],
    x64: i32,
    x65: i32,
    x66: &[i32],
    x67: i32,
    x68: i32,
    x69: &mut [i32],
    x70: i32,
    x71: i32,
)
    requires
        ((((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(old(x69), x70 as int, x71 as int))) && ((x70 == x64) && (x71
            == x65))) && ((x70 == x67) && (x71 == x68))) && ((forall|x121: i32|
            (forall|x122: i32|
                ((((#[trigger] ge_zero(x121) && (x121 < (x70 * x71))) && (#[trigger] ge_zero(x122) && (x122 < (x64//2B
                    * x65))))) as int != 0 ==> (true) as int != 0))) && (forall|x136: i32|
            (forall|x137: i32|
                ((((#[trigger] ge_zero(x136) && (x136 < (x70 * x71))) && (#[trigger] ge_zero(x137) && (x137 < (x67//2B
                    * x68))))) as int != 0 ==> (true) as int != 0))))),
    ensures
        ((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))) && (forall|x157: i32|
            ((((0 <= x157) && (x157 < (x70 * x71)))) as int != 0 ==> ((x69@[(x157) as int] == (
            x63@[(x157) as int] != 0 || x66@[(x157) as int] != 0) as int)) as int != 0))),//1
{
    assert(true);
    assert(true);
    let x73: i32 = x70 * x71;
    let mut x81: i32 = 0;
    while x81 < x73
        invariant
            x69@.len() >= (x70 * x71) - 1 + 1, //2C
            0 <= x81 <= x73,
            (forall|x82: i32|
                ((((0 <= x82) && (x82 < x81))) as int != 0 ==> ((x69@[(x82) as int] == (x63@[(
                x82) as int] !=0 || x66@[(x82) as int] !=0) as int)) as int != 0)),//1
        decreases x73 - x81,
    {
        let x94: i32 = x63[x81 as usize];
        let x95: i32 = x66[x81 as usize];
        let x96: i32 = if x94 != 0 || x95 != 0 {
            1
        } else {
            0
        };
        x69[x81 as usize] = x96;
        assert(true);
        assert(true);
        x81 += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn scalar_mult(
    x171: i32,
    x172: &[i32],
    x173: i32,
    x174: i32,
    x175: &mut [i32],
    x176: i32,
    x177: i32,
)
    requires
        ((((inv_matrix_Boolean(x172, x173 as int, x174 as int)) && (inv_matrix_Boolean(
            old(x175),
            x176 as int,
            x177 as int,
        ))) && ((x176 == x173) && (x177 == x174))) && (forall|x213: i32|
            (forall|x214: i32|
                ((((#[trigger] ge_zero(x213) && (x213 < (x176 * x177))) && (#[trigger] ge_zero(x214) && (x214 < (x173//2B
                    * x174))))) as int != 0 ==> (true) as int != 0)))),
        forall|i: i32|
            (0 <= i < x173 * x174) as int != 0 ==> (x172@[(i) as int] == 0 || x172@[(i) as int]
                == 1) as int != 0,
    ensures
        ((((inv_matrix_Boolean(x172, x173 as int, x174 as int)) && (inv_matrix_Boolean(
            x175,
            x176 as int,
            x177 as int,
        ))) && (forall|x233: i32|
            ((((0 <= x233) && (x233 < (x176 * x177)))) as int != 0 ==> ((x175@[(x233) as int] == (
            x171 !=0 && x172@[(x233) as int] != 0) as int)) as int != 0))) && (((x171 != 0 == false)) as int != 0 ==> ((//1
        forall|x247: i32|
            ((#[trigger] ge_zero(x247) && x247 < x176)) as int != 0 ==> ((forall|x250: i32|//2B
                ((#[trigger] ge_zero(x250) && x250 < x177)) as int != 0 ==> ((x175@[(((x247 * x177) + x250)) as int] !=0//1 //2B
                    == false)) as int != 0)) as int != 0)) as int != 0)),
{
    assert(true);
    let x179: i32 = x176 * x177;
    let mut x184: i32 = 0;
    while x184 < x179
        invariant
            x175@.len() >= (x176 * x177) - 1 + 1, //2C
            0 <= x184 <= x179,
            (forall|x185: i32|
                ((((0 <= x185) && (x185 < x184))) as int != 0 ==> ((x175@[(x185) as int] == (x171 !=0//1
                    && x172@[(x185) as int] != 0) as int)) as int != 0)), //1
        decreases x179 - x184,
    {
        let x197: i32;
        if x171 != 0 {
            let x196: i32 = x172[x184 as usize];
            x197 = x196;
        } else {
            x197 = 0;
        }
        x175[x184 as usize] = x197;
        assert(true);
        x184 += 1;
    }
}

fn main() {
}

} // verus!

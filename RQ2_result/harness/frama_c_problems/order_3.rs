#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn min3(x: int, y: int, z: int) -> int {
    if (x <= y && x <= z) {
        x
    } else {
        (if y <= z {
            y
        } else {
            z
        })
    }
}

pub open spec fn max3(x: int, y: int, z: int) -> int {
    if (x >= y && x >= z) {
        x
    } else {
        (if y >= z {
            y
        } else {
            z
        })
    }
}

pub open spec fn mid3(x: int, y: int, z: int) -> int {
    x + y + z - (min3(x as int, y as int, z as int)) - (max3(x as int, y as int, z as int))
}

fn CheckPost_order_3(old_a: &i32, old_b: &i32, old_c: &i32, a: &i32, b: &i32, c: &i32)
    requires
        ((a)@) <= ((b)@) <= ((c)@),
        (((old_a)@) == ((old_b)@) == ((old_c)@)) as int != 0 ==> ((((a)@) == ((b)@) == ((
        c)@))) as int != 0,
        ((a)@) == (min3(((old_a)@) as int, ((old_b)@) as int, ((old_c)@) as int)),
        ((b)@) == (mid3(((old_a)@) as int, ((old_b)@) as int, ((old_c)@) as int)),
        ((c)@) == (max3(((old_a)@) as int, ((old_b)@) as int, ((old_c)@) as int)),
{}


#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
        true,
    ensures
        ((a)@) <= ((b)@) <= ((c)@),
        (((old(a))@) == ((old(b))@) == ((old(c))@)) as int != 0 ==> ((((a)@) == ((b)@) == ((
        c)@))) as int != 0,
        ((a)@) == (min3(((old(a))@) as int, ((old(b))@) as int, ((old(c))@) as int)),
        ((b)@) == (mid3(((old(a))@) as int, ((old(b))@) as int, ((old(c))@) as int)),
        ((c)@) == (max3(((old(a))@) as int, ((old(b))@) as int, ((old(c))@) as int)),
{
    if *a > *b {
        let temp: i32 = *a;
        *a = *b;
        *b = temp;
    }
    if *a > *c {
        let temp: i32 = *a;
        *a = *c;
        *c = temp;
    }
    if *b > *c {
        let temp: i32 = *b;
        *b = *c;
        *c = temp;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn test() {
    let mut a1: i32 = 5;
    let mut b1: i32 = 3;
    let mut c1: i32 = 4;
    order_3(&mut a1, &mut b1, &mut c1);
    assert(a1 == 3 && b1 == 4 && c1 == 5);

    let mut a2: i32 = 2;
    let mut b2: i32 = 2;
    let mut c2: i32 = 2;
    order_3(&mut a2, &mut b2, &mut c2);
    assert(a2 == 2 && b2 == 2 && c2 == 2);

    let mut a3: i32 = 4;
    let mut b3: i32 = 3;
    let mut c3: i32 = 4;
    order_3(&mut a3, &mut b3, &mut c3);
    assert(a3 == 3 && b3 == 4 && c3 == 4);

    let mut a4: i32 = 4;
    let mut b4: i32 = 5;
    let mut c4: i32 = 4;
    order_3(&mut a4, &mut b4, &mut c4);
    assert(a4 == 4 && b4 == 4 && c4 == 5);
}

fn main() {
}

fn valid_test_harness_order_3() {
    // Test case 1: Distinct values
    let (a1, b1, c1) = (5, 3, 4);
    let (new_a1, new_b1, new_c1) = (3, 4, 5);
    CheckPost_order_3(&a1, &b1, &c1, &new_a1, &new_b1, &new_c1);

    // Test case 2: All equal
    let (a2, b2, c2) = (2, 2, 2);
    let (new_a2, new_b2, new_c2) = (2, 2, 2);
    CheckPost_order_3(&a2, &b2, &c2, &new_a2, &new_b2, &new_c2);

    // Test case 3: Duplicates in a and c
    let (a3, b3, c3) = (4, 3, 4);
    let (new_a3, new_b3, new_c3) = (3, 4, 4);
    CheckPost_order_3(&a3, &b3, &c3, &new_a3, &new_b3, &new_c3);

    // Test case 4: Already sorted
    let (a4, b4, c4) = (1, 2, 3);
    let (new_a4, new_b4, new_c4) = (1, 2, 3);
    CheckPost_order_3(&a4, &b4, &c4, &new_a4, &new_b4, &new_c4);

    // Test case 5: Single swap needed
    let (a5, b5, c5) = (3, 5, 4);
    let (new_a5, new_b5, new_c5) = (3, 4, 5);
    CheckPost_order_3(&a5, &b5, &c5, &new_a5, &new_b5, &new_c5);

    // Test case 8: Duplicate min values
    let (a8, b8, c8) = (3, 3, 4);
    let (new_a8, new_b8, new_c8) = (3, 3, 4);
    CheckPost_order_3(&a8, &b8, &c8, &new_a8, &new_b8, &new_c8);

    // Test case 9: Duplicate max values
    let (a9, b9, c9) = (2, 3, 3);
    let (new_a9, new_b9, new_c9) = (2, 3, 3);
    CheckPost_order_3(&a9, &b9, &c9, &new_a9, &new_b9, &new_c9);
}

} // verus!

// RAC
// fn order_3(a: &mut i32, b: &mut i32, c: &mut i32)
// {
//     if *a > *b {
//         let temp: i32 = *a;
//         *a = *b;
//         *b = temp;
//     }
//     if *a > *c {
//         let temp: i32 = *a;
//         *a = *c;
//         *c = temp;
//     }
//     if *b > *c {
//         let temp: i32 = *b;
//         *b = *c;
//         *c = temp;
//     }
// }

// fn test() {
//     let mut a1: i32 = 5;
//     let mut b1: i32 = 3;
//     let mut c1: i32 = 4;
//     order_3(&mut a1, &mut b1, &mut c1);
//     assert!(a1 == 3 && b1 == 4 && c1 == 5);

//     let mut a2: i32 = 2;
//     let mut b2: i32 = 2;
//     let mut c2: i32 = 2;
//     order_3(&mut a2, &mut b2, &mut c2);
//     assert!(a2 == 2 && b2 == 2 && c2 == 2);

//     let mut a3: i32 = 4;
//     let mut b3: i32 = 3;
//     let mut c3: i32 = 4;
//     order_3(&mut a3, &mut b3, &mut c3);
//     assert!(a3 == 3 && b3 == 4 && c3 == 4);

//     let mut a4: i32 = 4;
//     let mut b4: i32 = 5;
//     let mut c4: i32 = 4;
//     order_3(&mut a4, &mut b4, &mut c4);
//     assert!(a4 == 4 && b4 == 4 && c4 == 5);
// }

// fn main() {
//     valid_test_harness_order_3();
// }

// fn valid_test_harness_order_3() {
//     // Test case 1: Distinct values
//     let (mut a1, mut b1, mut c1) = (5, 3, 4);
//     order_3(&mut a1, &mut b1, &mut c1);

//     // Test case 2: All equal
//     let (mut a2, mut b2, mut c2) = (2, 2, 2);
//     order_3(&mut a2, &mut b2, &mut c2);

//     // Test case 3: Duplicates in a and c
//     let (mut a3, mut b3, mut c3) = (4, 3, 4);
//     order_3(&mut a3, &mut b3, &mut c3);

//     // Test case 4: Already sorted
//     let (mut a4, mut b4, mut c4) = (1, 2, 3);
//     order_3(&mut a4, &mut b4, &mut c4);

//     // Test case 5: Single swap needed
//     let (mut a5, mut b5, mut c5) = (3, 5, 4);
//     order_3(&mut a5, &mut b5, &mut c5);

//     // Test case 8: Duplicate min values
//     let (mut a8, mut b8, mut c8) = (3, 3, 4);
//     order_3(&mut a8, &mut b8, &mut c8);

//     // Test case 9: Duplicate max values
//     let (mut a9, mut b9, mut c9) = (2, 3, 3);
//     order_3(&mut a9, &mut b9, &mut c9);
// }

// fn invalid_test_harness_order_3() {
//     // Test case 6: Invalid - NULL pointer simulation
//     // order_3(None, &3, &4);
    
//     // Test case 7: Invalid - Overlapping pointers (Violation: \separated)
//     let x = 5; let c = 4;
//     // order_3(&x, &x, &c);
// }

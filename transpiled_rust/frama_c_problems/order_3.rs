fn order_3(a: &mut i32, b: &mut i32, c: &mut i32) {
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

fn test() {
    let mut a1: i32 = 5;
    let mut b1: i32 = 3;
    let mut c1: i32 = 4;
    order_3(&mut a1, &mut b1, &mut c1);
    // verus_assert(1);
    
    let mut a2: i32 = 2;
    let mut b2: i32 = 2;
    let mut c2: i32 = 2;
    order_3(&mut a2, &mut b2, &mut c2);
    // verus_assert(2);

    let mut a3: i32 = 4;
    let mut b3: i32 = 3;
    let mut c3: i32 = 4;
    order_3(&mut a3, &mut b3, &mut c3);
    // verus_assert(3);

    let mut a4: i32 = 4;
    let mut b4: i32 = 5;
    let mut c4: i32 = 4;
    order_3(&mut a4, &mut b4, &mut c4);
    // verus_assert(4);
}
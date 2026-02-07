fn array_swap(x0: &mut [i32]) {
    let x2: i32 = x0[0];
    let x3: i32 = x0[1];
    x0[0] = x3;
    x0[1] = x2;
}
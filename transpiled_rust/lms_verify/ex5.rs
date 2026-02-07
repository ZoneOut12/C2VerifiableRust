fn array_swap(p: &mut [i32]) {
    let tmp: i32 = p[0];
    p[0] = p[1];
    p[1] = tmp;
}
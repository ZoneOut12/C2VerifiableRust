fn function(mut x: i32, mut y: i32) -> i32 {
    let res: i32;
    y += 10;
    x -= 5;
    res = x + y;
    // verus_assert(1);
    res
}
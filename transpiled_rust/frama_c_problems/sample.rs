fn fun(x: i32, y: i32) -> i32 {
    let mut r: i32 = x;
    let mut d: i32 = 0;
    
    while r >= y {
        r = r - y;
        d = d + 1;
    }
    d
}

fn main() {
    let res: i32 = fun(10, 2);
    // verus_assert(1);
}
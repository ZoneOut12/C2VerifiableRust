fn mul(a: i32, b: i32) -> i32 {
    let mut x: i32 = a;
    let mut prod: i32 = 0;
    while x > 0 {
        // verus_assert(1);
        // verus_assert(2);
        prod = prod + b;
        x -= 1;
    }
    prod
}

fn main() {
    let pdt: i32 = mul(2, 5);
    // verus_assert(3);
}
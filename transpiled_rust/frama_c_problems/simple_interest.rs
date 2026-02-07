fn simple(p: i32, n: i32, r: i32) -> i32 {
    let si: i32 = p * n * r / 100;
    si
}

fn main() {
    let s: i32 = simple(10000, 3, 10);
}
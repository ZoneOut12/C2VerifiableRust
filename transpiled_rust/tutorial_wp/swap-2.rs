static mut h: i32 = 42;

fn swap(a: &mut i32, b: &mut i32) {
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

fn main() {
    let mut a: i32 = 37;
    let mut b: i32 = 91;

    // verus_assert(1);
    swap(&mut a, &mut b);
    // verus_assert(2);
}
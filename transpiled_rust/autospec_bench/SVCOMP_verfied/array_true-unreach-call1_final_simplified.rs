fn main() {
    let mut A: [i32; 2048] = [0; 2048];
    let mut i: i32 = 0;
    while i < 1024 {
        A[i as usize] = i;
        i += 1;
    }
    // verus_assert(1);
}
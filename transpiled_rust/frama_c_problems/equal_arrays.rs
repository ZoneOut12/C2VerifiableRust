fn check(a: &[i32], b: &[i32], n: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if a[i as usize] != b[i as usize] {
            return 0;
        }
        i += 1;
    }
    return 1;
}

fn main() {
    let a: [i32; 5] = [1, 2, 3, 4, 5];
    let b: [i32; 5] = [1, 2, 3, 4, 5];
    check(&a, &b, 5);
}
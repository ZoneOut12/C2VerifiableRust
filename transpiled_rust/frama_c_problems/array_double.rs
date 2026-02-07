fn arrayDouble(a: &mut [i32], n: i32) {
    let mut p: i32 = 0;
    while p < n {
        a[p as usize] = a[p as usize] * 2;
        p = p + 1;
    }
}

fn main() {
    let mut arr: [i32; 6] = [0, 1, 2, 3, 4, 5];
    arrayDouble(&mut arr, 6);
}
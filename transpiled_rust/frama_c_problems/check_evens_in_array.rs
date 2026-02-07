fn areElementsEven(a: &[i32], n: i32) -> i32 {
    let mut p: i32 = 0;
    while p < n {
        if a[p as usize] % 2 != 0 {
            return 0;
        }
        p += 1;
    }
    return 1;
}

fn main() {
    let arr: [i32; 5] = [2, 4, 6, 8, 10];
    let res: i32 = areElementsEven(&arr, 5);
    // verus_assert(1);
}
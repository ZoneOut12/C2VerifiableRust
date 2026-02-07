fn bubbleSort(a: &mut [i32], n: i32) {
    let mut i: i32;
    let mut j: i32;

    i = n - 1;
    while i > 0 {
        j = 0;
        while j < i {
            if a[j as usize] > a[(j + 1) as usize] {
                let temp: i32 = a[j as usize];
                a[j as usize] = a[(j + 1) as usize];
                a[(j + 1) as usize] = temp;
            }
            j += 1;
        }
        i -= 1;
    }
}
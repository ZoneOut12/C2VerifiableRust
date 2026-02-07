fn foo(a: &[i32; 10]) {
    let mut g: [i32; 10] = [0; 10];

    {
        let mut i: i32 = 0;
        while i < 10 {
            g[i as usize] = a[i as usize];
            i += 1;
        }
    }

    {
        let mut i: i32 = 0;
        while i < 10 {
            i += 1;
        }
    }
}
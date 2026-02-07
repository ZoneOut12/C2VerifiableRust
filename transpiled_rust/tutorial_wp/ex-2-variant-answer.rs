fn foo() {
    let mut x: i32 = -20;

    
    while x < 0 {
        x += 4;
    }
}

fn bar() {
    let mut x: i32 = -20;
    let mut i: i32 = 5;

    
    while x < 0 {
        x += 4;
        i -= 1;
    }
}
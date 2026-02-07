fn function(a: i32, x: i32) -> i32 {
    a * x + 4
}

fn foo(a: i32, x: i32, y: i32) {
    let mut fmin: i32;
    let mut fmax: i32;
    if x < y {
        fmin = function(a, x);
        fmax = function(a, y);
    } else {
        fmin = function(a, y);
        fmax = function(a, x);
    }
    // verus_assert(1);
}
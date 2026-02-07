fn abs(x: i32) -> i32 {
    if x >= 0 { x } else { -x }
}

fn distance(a: i32, b: i32) -> i32 {
    abs(b - a)
}

fn distances(a: &[i32], b: &[i32], result: &mut [i32], len: usize) {
    let mut i: usize = 0;
    while i < len {
        result[i] = distance(a[i], b[i]);
        i += 1;
    }
}

struct client;

fn initialize(c: &mut client) {
    unimplemented!()
}

fn connect(c: &mut client) -> i32 {
    unimplemented!()
}

fn prepare(c: &mut client) -> i32 {
    initialize(c);
    connect(c)
}

fn terminates_f1(x: i32) {
    if x <= 0 {
        while true {
        }
    }
}

fn terminates_f2(x: i32) {
    if x <= 0 {
        while true {
        }
    }
}
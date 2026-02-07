#[derive(Copy, Clone)]
enum note {
    N500,
    N200,
    N100,
    N50,
    N20,
    N10,
    N5,
    N2,
    N1,
}

use note::*;

const values: [i32; 9] = [500, 200, 100, 50, 20, 10, 5, 2, 1];

fn remove_max_notes(n: note, rest: &mut i32) -> i32 {
    let num: i32 = *rest / values[n as usize];
    *rest -= num * values[n as usize];
    num
}

fn make_change(amount: i32, received: i32, change: &mut [i32]) -> i32 {
    if amount > received {
        return -1;
    }
    let mut rest: i32 = received - amount;

    change[N500 as usize] = remove_max_notes(N500, &mut rest);
    change[N200 as usize] = remove_max_notes(N200, &mut rest);
    change[N100 as usize] = remove_max_notes(N100, &mut rest);
    change[N50 as usize] = remove_max_notes(N50, &mut rest);
    change[N20 as usize] = remove_max_notes(N20, &mut rest);
    change[N10 as usize] = remove_max_notes(N10, &mut rest);
    change[N5 as usize] = remove_max_notes(N5, &mut rest);
    change[N2 as usize] = remove_max_notes(N2, &mut rest);
    change[N1 as usize] = remove_max_notes(N1, &mut rest);

    0
}
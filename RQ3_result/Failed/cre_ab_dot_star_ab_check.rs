#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn matcher_ab_dot_star_ab(x0: &str) -> (result: i32)
    requires
        (((((x0)@.len() - 1)) >= 0) && ((forall|i: int|
            0 <= i < x0@.len() - 1 ==> (x0@[(i) as int] != '\0')) && x0@[x0@.len() - 1] == '\0')),
{
    let bytes = x0.as_bytes();
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    let mut x4: usize = 0;
    loop
        invariant
            (((((x4)@.len() - 1)) >= 0) && x4@.len() >= (((x4)@.len() - 1)) + 1),
        decreases
                (((((x4)@.len() - 1)) + (if (x2) {
                    (0)
                } else {
                    (1)
                })) + (if (x3) {
                    (1)
                } else {
                    (0)
                })),
    {
        let x5: i32 = x2;
        let x9: i32;
        if x5 != 0 {
            x9 = 0;
        } else {
            let x7: i32 = x3;
            x9 = x7;
        }
        if x9 == 0 {
            break ;
        }
        let x12: u8;
        if x4 < bytes.len() {
            x12 = bytes[x4];
        } else {
            x12 = 0;
        }
        let x13: i32 = if x12 == 0 {
            1
        } else {
            0
        };
        let x16: i32;
        if x13 != 0 {
            x16 = 0;
        } else {
            let x15: i32 = if x12 == b'a' {
                1
            } else {
                0
            };
            x16 = x15;
        }
        let x88: i32;
        if x16 != 0 {
            let x17: usize = x4 + 1;
            let x18: u8;
            if x17 < bytes.len() {
                x18 = bytes[x17];
            } else {
                x18 = 0;
            }
            let x19: i32 = if x18 == 0 {
                1
            } else {
                0
            };
            let x22: i32;
            if x19 != 0 {
                x22 = 0;
            } else {
                let x21: i32 = if x18 == b'b' {
                    1
                } else {
                    0
                };
                x22 = x21;
            }
            let x87: i32;
            if x22 != 0 {
                let x23: usize = x17 + 1;
                let mut x26: usize = x23;
                let mut x24: i32 = 0;
                let mut x25: i32 = 1;
                loop
                    invariant
                        (((((x26)@.len() - 1)) >= 0) && x26@.len() >= (((x26)@.len() - 1)) + 1),
                    decreases
                            (((((x26)@.len() - 1)) + (if (x24) {
                                (0)
                            } else {
                                (1)
                            })) + (if (x25) {
                                (1)
                            } else {
                                (0)
                            })),
                {
                    let x27: i32 = x24;
                    let x31: i32;
                    if x27 != 0 {
                        x31 = 0;
                    } else {
                        let x29: i32 = x25;
                        x31 = x29;
                    }
                    if x31 == 0 {
                        break ;
                    }
                    let x33: usize = x26;
                    let x34: u8;
                    if x33 < bytes.len() {
                        x34 = bytes[x33];
                    } else {
                        x34 = 0;
                    }
                    let x35: i32 = if x34 == 0 {
                        1
                    } else {
                        0
                    };
                    let x38: i32;
                    if x35 != 0 {
                        x38 = 0;
                    } else {
                        let x37: i32 = if x34 == b'a' {
                            1
                        } else {
                            0
                        };
                        x38 = x37;
                    }
                    let x47: i32;
                    if x38 != 0 {
                        let x39: usize = x33 + 1;
                        let x40: u8;
                        if x39 < bytes.len() {
                            x40 = bytes[x39];
                        } else {
                            x40 = 0;
                        }
                        let x41: i32 = if x40 == 0 {
                            1
                        } else {
                            0
                        };
                        let x44: i32;
                        if x41 != 0 {
                            x44 = 0;
                        } else {
                            let x43: i32 = if x40 == b'b' {
                                1
                            } else {
                                0
                            };
                            x44 = x43;
                        }
                        let x46: i32 = if x44 != 0 {
                            1
                        } else {
                            0
                        };
                        x47 = x46;
                    } else {
                        x47 = 0;
                    }
                    x24 = x47;
                    let x49: i32 = x24;
                    if x49 != 0 {
                    } else {
                        let x36: i32 = if x35 != 0 {
                            0
                        } else {
                            1
                        };
                        x25 = x36;
                        let x52: i32 = x25;
                        if x52 != 0 {
                            x25 = 1;
                            let x39: usize = x33 + 1;
                            x26 = x39;
                        }
                    }
                }
                x87 = x24;
            } else {
                x87 = 0;
            }
            x88 = x87;
        } else {
            x88 = 0;
        }
        x2 = x88;
        let x90: i32 = x2;
        if x90 != 0 {
        } else {
            let x14: i32 = if x13 != 0 {
                0
            } else {
                1
            };
            x3 = x14;
            let x93: i32 = x3;
            if x93 != 0 {
                let x17: usize = x4 + 1;
                x4 = x17;
            }
        }
    }
    let x124: i32 = x2;
    x124
}

fn main() {
}

} // verus!

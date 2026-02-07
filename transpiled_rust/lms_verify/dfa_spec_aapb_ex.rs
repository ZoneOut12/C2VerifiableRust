fn lemma_star_A_all(s: &str, i: i32, j: i32) {
  let mut x = i;
  
  while x < j {
    x += 1;
  }
}

fn lemma_all_star_A(s: &str, i: i32, j: i32) {
  let mut x = j;
  
  while i < x {
    x -= 1;
  }
}

fn lemma_star_A_not(s: &str, i: i32, m: i32, j: i32) {
  let mut x = m;
  
  while i < x {
    x -= 1;
  }
}

fn lemma_star_A_dec(s: &str, i: i32, j: i32) {
  
}

fn lemma_star_A(s: &str, i: i32, j: i32, n: i32) {
  let mut x = j;
  
  while i < x {
    x -= 1;
  }
}

fn lemma01(s: &str, i: i32, j: i32) {
}

fn lemma11(s: &str, i: i32, j: i32) {
}

fn lemma12(s: &str, i: i32, j: i32) {
}

fn lemma2f(s: &str, i: i32, j: i32) {
}

fn m_aapb(s: &str) -> i32 {
  let s_bytes = s.as_bytes();
  let mut cur = 0;
  let mut id = 0;
  let mut m = 1;
  
  while cur < s_bytes.len() && m != 0 {
    m = 0;
    if id == 0 {
      if s_bytes[cur] == b'A' {
        id = 1;
        m = 1;
      }
    } else if id == 1 {
      if s_bytes[cur] == b'A' {
        id = 1;
        m = 1;
      } else if s_bytes[cur] == b'B' {
        id = 2;
        m = 1;
      }
    } else if id == 2 {
    } else {
    }
    cur += 1;
  }
  let res = (id == 2) as i32 & (cur == s_bytes.len()) as i32 & m;
  res
}
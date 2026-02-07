fn factorial(n: i32) -> i32 {
  let mut i: i32 = 1;
  let mut f: i32 = 1;
  
  while i <= n  {
    f = f * i;
    i = i + 1;
  }
  f
}
int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant n != c;
  loop invariant c >= 0 && c <= n;
  loop invariant c > n ==> c == n;
  loop invariant c > n ==> c == n + 1;
  loop invariant c <= n;
  loop invariant \forall integer k; 1 <= k <= c ==> (\exists integer i; 1 <= i <= n && i == c);
  loop invariant 0 <= c;
  loop assigns n;
  loop assigns c;
  */
  while (unknown()) {  
    if (unknown()) {
      if (c > n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c = 1;
      }
    }
  }
  if (c < 0) {
    if (c > n) {
      //@ assert c == n;
    }
  }
}

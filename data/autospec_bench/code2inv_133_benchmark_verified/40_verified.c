int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;

  /*@
  loop invariant c <= n;
  loop invariant c <= n || c == 1;
  loop invariant 0 <= c;
  loop invariant (c <= n && c >= 0) || (c == n+1);
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c  = c + 1;
      }
    } else {
      if (c == n) {
        c  = 1;
      }
    }
  }
  if ( (c != n) ) {
    //@ assert  (c >= 0) ;
  }
}

int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == n ==> \forall integer k; 0 <= k < c ==> k != n;
  loop invariant c != n || c <= n;
  loop invariant 0 <= c;
  loop invariant (c == n) ==> (n > -1);
  loop assigns n;
  loop assigns c;
  */
  while (unknown()) {
      if(unknown()) {
        if(c != n) {
          if (c >= 2147483647) break;
          (c = (c + 1));
        }
      } else {
        if (c == n) {
          c = 1;
        }
      }
  }
  if(c == n) {
    //@ assert n > -1;
  }
}

/*@
requires (x == 10000);
*/
void foo(int x) {
  /*@
  loop invariant x <= 10000;
  loop invariant 0 <= x;
  loop assigns x;
  loop variant x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }
  //@ assert  (x == 0) ;
}

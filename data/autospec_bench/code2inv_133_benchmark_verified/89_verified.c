int unknown();

/*@
requires x == y;
*/
void foo(int x, int y) {
  int lock = 1;
  
  /*@
  loop invariant x == y;
  loop invariant lock == 1;
  loop invariant lock == 1 || lock == 0;
  loop invariant lock == 0 || lock == 1;
  loop invariant lock != 1 ==> x == y;
  loop invariant (lock == 1) || (lock == 0);
  loop assigns y;
  loop assigns x;
  loop assigns lock;
  */
  while (x != y) {  
    if (unknown()) {
      lock = 1;
      x = y;
    } else {
      lock  = 0;
      x  = y;
      y  = y + 1; 
    }
  }
  //@ assert lock == 1;
}

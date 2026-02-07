#include<limits.h>

int unknown();

/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  /*@
  loop invariant x == 20 ==> y != 0;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    if (x > 2147483647 - 10 || y > 2147483647 - 10){
      break;
    }
    x  = x + 10;
    y  = y + 10;
  }
  if (x == 20) {
    //@ assert y != 0;
  }
}

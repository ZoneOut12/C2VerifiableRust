#include<limits.h>
void main() {
  long long x;
  long long y;
  x = 1;
  y = 0;
  /*@
  loop invariant y <= x;
  loop invariant y <= 100000;
  loop invariant x == ((y - 1) * y) / 2 + 1;
  loop invariant 1 <= x;
  loop invariant 0 <= y;
  loop assigns y;
  loop assigns x;
  loop variant 100000 - y;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }
  //@ assert  (x >= y) ;
}

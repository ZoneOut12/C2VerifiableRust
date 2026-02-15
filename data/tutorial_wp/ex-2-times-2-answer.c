#include <limits.h>

/*@ 
  requires 0 <= x <= INT_MAX / 2;
  assigns  \nothing ;
  ensures  \result == 2 * x ;
*/
int times_2(int x){
  int r = 0 ;
  int i = 0 ;

  L: ;
  
  /*@
    loop invariant 0 <= x ;
    loop invariant r == 2 * i ;
    loop invariant i + x == \at(i + x, L) ;
    loop assigns r, x, i ;
    loop variant x ;
  */
  while(x > 0){
    r += 2 ;
    x -- ;
    i++ ;
  }
  return r;
}

typedef int (*arith_op)(int, int);

/*@ requires -1000000 <= x <= 1000000;
    requires -1000000 <= y <= 1000000;
    assigns \nothing;
    ensures \result == x + y;
*/
int arith_add(int x, int y)
{
    return x + y;
}

/*@ requires -1000000 <= x <= 1000000;
    requires -1000000 <= y <= 1000000;
    assigns \nothing;
    ensures \result == x - y;
*/
int arith_sub(int x, int y)
{
    return x - y;
}

/*@ requires op == &arith_add || op == &arith_sub;
    requires -1000000 <= x <= 1000000;
    requires -1000000 <= y <= 1000000;
    assigns \nothing;
    ensures op == &arith_add ==> \result == x + y;
    ensures op == &arith_sub ==> \result == x - y;
*/
int arith_apply(arith_op op, int x, int y)
{
    if (op == &arith_add) return arith_add(x, y);
    return arith_sub(x, y);
}

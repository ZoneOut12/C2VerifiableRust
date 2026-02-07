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

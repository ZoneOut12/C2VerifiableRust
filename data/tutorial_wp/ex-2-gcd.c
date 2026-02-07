#include <limits.h>

/*@ inductive is_gcd(integer a, integer b, integer d) {
    case gcd_zero:
      \forall integer n; is_gcd(n, 0, n);
    case gcd_succ:
      \forall integer a, b, d; 
      is_gcd(b, a % b, d) ==> is_gcd(a, b, d);
    }
*/

/*@
  requires a >= 0 && b >= 0 ;
  assigns \nothing ;
  ensures is_gcd(a, b, \result) ;
*/
unsigned gcd(unsigned a, unsigned b){
  unsigned a_pre = a;
  unsigned b_pre = b;
  /*@
    loop invariant a >= 0 && b >= 0 ;
    loop invariant \forall integer t ; is_gcd(a, b, t) ==> is_gcd(a_pre, b_pre, t) ;
    loop assigns a, b ;
    loop variant b ;
  */ 
  while (b != 0){
    unsigned t = b;
    b = a % b;
    a = t;
  }
  return a;
}

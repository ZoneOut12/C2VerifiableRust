/* run.config
   DEPS: @PTEST_DEPS@ @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@/interactive/*.v
   STDOPT:+"-wp-no-rte -wp-prover alt-ergo,coq -wp-session @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@"
*/

#include <limits.h>

/*@
  inductive is_power(integer x, integer n, integer r) {
  case zero: \forall integer x ; is_power(x, 0, 1) ;
  case N: \forall integer x, n, r ; n > 0 ==> is_power(x, n-1, r) ==> is_power(x, n, r*x) ;
  }
*/

/*@
  axiomatic Power{
    axiom power_even:
        \forall integer x, n, r ;
        n >= 0 ==> is_power(x * x, n, r) ==> is_power(x, n * 2, r) ;

    axiom power_odd:
        \forall integer x, n, rp ;
        n >= 0 ==> is_power(x * x, n, rp) ==> is_power(x, 2 * n + 1, x * rp) ;
    axiom monotonic:
        \forall integer x, n1, n2, r1, r2;
        0 <= n1 <= n2 ==> is_power(x, n1, r1) && is_power(x, n2, r2) ==> r1 <= r2;
  }
*/

/*@
  requires 0 <= n < INT_MAX ;
  requires \exists integer m; is_power(x, n, m) && INT_MIN <= m <= INT_MAX;
  assigns \nothing ;
  ensures is_power(x, n, \result);
*/
int power(int x, int n){
  int r = 1 ;

  /*@
    loop invariant 1 <= i <= n+1 ;
    loop invariant is_power(x, i-1, r) ;
    loop assigns i, r ;
    loop variant n - i ;
  */
  for(int i = 1 ; i <= n ; ++i){
    r *= x ;
  }

  return r ;
}

/*@
  assigns \nothing ;
  ensures is_power(x, n, \result);
*/
unsigned fast_power(unsigned x, unsigned n){
  //@ ghost unsigned n_pre = n;
  unsigned r = 1 ;
  unsigned p = x ;

  /*@
    loop invariant 0 <= n ;
    loop invariant \forall integer v ; is_power(p, n, v) ==> is_power(x, n_pre, r * v) ;
    loop assigns n, r, p ;
    loop variant n ;
  */
  while(n > 0){
    if(n % 2 == 1){
        //@ assert is_power(p, n, r);
        r = r * p ;
    }
    p *= p ;
    n /= 2 ;
  }
  //@ assert is_power(p, n, 1) ;

  return r ;
}
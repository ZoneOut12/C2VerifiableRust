#include <stdio.h>
#include <limits.h>

/*@
  axiomatic Factorial {
  logic integer fact(integer n);
  
  axiom case_n:
    \forall integer n;
    n >= 1 ==> fact(n) == n*fact(n-1);
  axiom case_0:
    fact(0) == 1;
  axiom monotonic:
    \forall integer n;
    n >= 0 ==> fact(n+1) > fact(n);
  }
*/

/*@
  requires  0 <= n < INT_MAX;
  ensures   \result == fact(n);
  assigns   \nothing ; 
*/
int factorial(int n) {
  int i = 1;
  int f = 1;
  /*@
    loop invariant f == fact(i-1);
    loop invariant 0 < i;
    loop invariant i <= n+1;
    loop assigns i, f;
    loop variant n + 1 - i;
  */
  while (i <= n)  {
    f = f * i;
    i = i + 1;
  }
  return f;
}
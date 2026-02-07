#include <assert.h>
#include <limits.h>
/*
 * "nested4.c" from InvGen benchmark suite
 */

/*@
  requires l > 0;
  requires n > l;
*/
void foo(int n, int l) {
  int i,k;


  /*@
  loop invariant 1 <= k <= n;
  loop assigns k;
  loop assigns i;
  loop variant n - k;
  */
  for (k=1; k<n; k++){
    /*@
    loop invariant l <= i <= n;
    loop assigns i;
    loop variant n - i;
    */
    for (i=l; i<n; i++) {
    }
    /*@
    loop invariant l <= i <= n;
    loop assigns i;
    loop variant n - i;
    */
    for (i=l; i<n; i++) {
      //@ assert 1<=i;
    }
  }

}

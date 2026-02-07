// Source: Michael Colon, Sriram Sankaranarayanan, Henny Sipma: "Linear
// Invariant Generation using Non-Linear Constraint Solving", CAV 2003.
#include "assert.h"

# define LARGE_INT 10

/*@ 
requires 0 <= k && k <= 1;
*/
int foo(int k) {
    int i,j;
    i = 1;
    int tmp = k;
    /*@
    loop invariant i == k + 2 * (i - 1) || i== k + 1 + 2 * (i - 1);
    loop invariant i + k <= 2;
    loop invariant 1 <= i;
    loop invariant 1 <= i + k;
    loop assigns k;
    loop assigns j;
    loop assigns i;
    loop variant LARGE_INT - i;
    */
    while (i < LARGE_INT) {
        i = i + 1;
        k = k - 1;
        //@ assert 1 <= i + k && i + k <= 2 && i >= 1;
    }
    return 0;
}
#include <limits.h>
/*@
    requires n>=0;
    requires n/2*(n/2+1) <= INT_MAX;
    ensures \result == n/2*(n/2+1);
    assigns \nothing;
*/
int func(int n) {
    int sum = 0;
    int i = 0;
    /*@
        loop invariant i <= n/2 + 1;
        loop invariant (sum == i*(i-1));
        loop assigns sum, i;
        loop variant n/2 - i;
    */
    while(i <= n/2) {
        sum = sum + 2*(i);
        i++;
    }
    //@ assert i == n/2 + 1;
    return sum;
}
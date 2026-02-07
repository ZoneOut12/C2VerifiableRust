#include <limits.h>
#include <stdlib.h>

/*@
    requires val > INT_MIN;
    ensures \result >= 0;
    ensures (val >= 0 ==> \result == val) && 
            (val < 0 ==> \result == -val);
*/
int my_abs(int val) {
    return abs(x);
}

/*@
    requires a > INT_MIN;
*/
void foo(int a) {
    int b = my_abs(-42);
    int c = my_abs(42);
    int d = my_abs(a);
}
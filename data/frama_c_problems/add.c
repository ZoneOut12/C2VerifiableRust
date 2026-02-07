#include <limits.h>
/*@
    requires x+y <= INT_MAX;
    requires x+y >= INT_MIN;
    ensures \result == x+y;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
}
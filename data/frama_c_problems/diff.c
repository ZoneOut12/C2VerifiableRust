#include <limits.h>
/*@
    requires INT_MIN <= x-y <= INT_MAX;
    ensures y == x-\result;
*/


int diff (int x, int y) {
    return x-y;
}

int main() {
    int t = diff(10, 5);
    //@ assert t == 5;
    return 0;
}
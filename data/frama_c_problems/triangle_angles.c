#include <limits.h>
/*@
    requires INT_MIN <= a+b <= INT_MAX && INT_MIN <= a+b+c <= INT_MAX;
    behavior valid:
        assumes (a+b+c == 180) && a > 0 && b > 0 && c > 0;
        ensures \result == 1;
    behavior invalid:
        assumes !((a+b+c == 180) && a > 0 && b > 0 && c > 0);
        ensures \result == 0;
    disjoint behaviors;
    complete behaviors;
*/
int triangle(int a, int b, int c) {
    if ((a+b+c == 180) && a > 0 && b > 0 && c > 0) {
        return 1;
    } else {
        return 0;
    }
}

void check_validity() {
    int res = triangle(90, 45, 45);
    //@ assert res == 1;
}

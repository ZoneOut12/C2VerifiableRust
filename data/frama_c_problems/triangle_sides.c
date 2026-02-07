#include <stdio.h>
#include <limits.h>
/*@
    requires a>0 && b>0 && c>0;
    requires a+b+c <= INT_MAX;
    behavior valid:
        assumes (a+b>c) && (a+c>b) && (b+c>a);
        ensures \result == 1;
    behavior invalid:
        assumes !((a+b>c) && (a+c>b) && (b+c>a));
        ensures \result == 0;
    disjoint behaviors;
    complete behaviors;
*/

int validts(int a, int b, int c) {
    int valid = 0;
    if ((a+b>c) && (a+c>b) && (b+c>a)) {
        valid = 1;
    } else {
        valid = 0;
    }
    return valid;
}

void test() {
    int valid = validts(2,3,4);
    //@ assert valid == 1;
}





#include <stdio.h>
#include <limits.h>

/*@
    requires a >= 0 && b >= 0;
    requires a*b <= INT_MAX;
    ensures \result == a*b;
    assigns \nothing;
*/
int mul(int a, int b) {
    int x = a, prod = 0;
    /*@ 
        loop invariant x >= 0;
        loop invariant prod == (a-x)*b;
        loop assigns prod, x;
        loop variant x;
    */
    while(x > 0) {
        //@ assert x >= 1 && prod == (a-x)*b;
        //@ assert prod <= a*b - b;
        prod = prod + b;
        x--;
    }
    return prod;
}

int main() {
    int pdt = mul(2, 5);
    //@ assert pdt == 10;
}
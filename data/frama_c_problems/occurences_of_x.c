#include <limits.h>
/*@
    requires n > 0 && x > 0;
    requires n*x <= INT_MAX;
    requires \valid(sum);
    requires \valid_read(a + (0..n-1));
    ensures \result >= 0 && \result <= n;
*/
int func(int *a, int n, int x, int *sum) {
    int p = 0;
    int count = 0;
    *sum = 0;
    /*@
        loop invariant 0 <= p <= n;
        loop invariant 0 <= count <= p && *sum == count*x;
        loop invariant *sum <= n*x;
        loop assigns p, count, *sum;
        loop variant n - p;
    */
    while (p < n) {
        if (a[p] == x) {
            count = count + 1;
            *sum = *sum + x;
        }
        p = p + 1;
    }
    Label_a:
    *sum += 0;
    //@ assert \at(*sum, Label_a) == count*x;
    return count;
}

typedef int (*binop_func)(int, int);

/*@ requires -1000000 <= a <= 1000000;
    requires -1000000 <= b <= 1000000;
    assigns \nothing;
    ensures \result == a + b;
*/
int fp_add(int a, int b)
{
    return a + b;
}

/*@ requires -1000000 <= a <= 1000000;
    requires -1000000 <= b <= 1000000;
    assigns \nothing;
    ensures \result == a - b;
*/
int fp_sub(int a, int b)
{
    return a - b;
}

/*@ requires op == &fp_add || op == &fp_sub;
    requires -1000000 <= a <= 1000000;
    requires -1000000 <= b <= 1000000;
    assigns \nothing;
    ensures op == &fp_add ==> \result == a + b;
    ensures op == &fp_sub ==> \result == a - b;
*/
int fp_apply(binop_func op, int a, int b)
{
    if (op == &fp_add) return fp_add(a, b);
    return fp_sub(a, b);
}


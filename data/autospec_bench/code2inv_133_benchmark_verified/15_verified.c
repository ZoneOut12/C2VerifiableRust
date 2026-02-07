/*@
requires n > 0;
*/
void foo(int n)
{
    int x = 0;
    int m = 0;

    /*@
    loop invariant x <= n;
    loop invariant n > 0 ==> m >= 0;
    loop invariant n > 0 ==> m < n;
    loop invariant m <= x;
    loop invariant 0 <= x;
    loop assigns x;
    loop assigns m;
    loop variant n - x;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    if(n > 0) {
       //@ assert m < n;
       //@ assert m >= 0;
    }
}

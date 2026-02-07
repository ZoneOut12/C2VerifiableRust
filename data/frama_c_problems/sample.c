/*@
    requires x >= 0 && y > 0;
    ensures \result == x/y;
*/
int fun(int x, int y) {
    int r = x;
    int d = 0;
    /*@
        loop invariant r >= 0;
        loop invariant r + d*y == x;
        loop assigns r, d;
        loop variant r-y;
    */
    while (r >= y) {
        // Beginning
        r = r - y;
        d = d + 1;
        // ENd
    }
    return d;
}

int main() {
    int res = fun(10, 2);
    //@ assert res == 5;
}
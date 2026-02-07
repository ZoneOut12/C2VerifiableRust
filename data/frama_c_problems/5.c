/*@
    requires x >= y && x > 0 && y > 0;
    requires \valid(r);
    ensures *r < y;
    ensures x == \result*y + *r;
    
*/
int fun(int x, int y , int *r) {
    *r = x;
    int d = 0;
    /*@
        loop invariant  *r == x - y*d;
        loop assigns *r, d;
        loop variant *r;
    */
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
    return d;
}
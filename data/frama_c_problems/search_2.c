/*@
    requires n > 0;
    requires \valid_read(a + (0..n-1));
    assigns \nothing;

    behavior present:
        assumes \exists integer k; 0 <= k < n && x == a[k];
        ensures \result == 1;

    behavior not_present:
        assumes  \forall integer k; 0 <= k < n ==> x != a[k];
        ensures \result == 0;
*/
int arraySearch(int *a, int x, int n) {
    int p = 0;
    /*@
        loop invariant  0 <= p <= n;
        loop invariant \forall integer k; 0 <= k < p ==> x != a[k];
        loop assigns p;
        loop variant n - p;
    */
    while (p < n) {
        if (a[p] == x) {
            return 1;
        }
        if (p == (n-1))
            break;
        p++;
    }
    return 0;
}
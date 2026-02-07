/*@
    requires n > 0;
    requires \valid(a + (0..n-1));
    assigns a[0..n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] == \old(a[n-k-1]);
*/
void reverse(int *a, int n) {
    int i = 0;
    int j = n-1;
    /*@
        loop invariant 0 <= i <= n/2;
        loop invariant j == n - 1 - i;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == \at(a[n-k-1], Pre) && a[n-k-1] == \at(a[k], Pre);
        loop invariant \forall integer k; i <= k <= n-i-1 ==> a[k] == \at(a[k], Pre);
        loop invariant \forall integer k; n-i < k < n ==> a[k] == \at(a[n-k-1], Pre) && a[n-k-1] == \at(a[k], Pre);
        loop assigns a[0..(n-1)], i, j;
        loop variant n/2 - i;
    */
    while (i < n/2) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
        i++;
        j--;
    }
}
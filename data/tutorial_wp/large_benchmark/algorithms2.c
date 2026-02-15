/*****************************************************************************
 * Formally Verified Algorithms in C with ACSL Annotations (Part 2)
 *
 * Verify with: frama-c -wp -wp-rte algorithms2.c
 *
 * No recursive, inductive, axiomatic definitions, or \at used.
 * No sorting algorithms.
 *****************************************************************************/

#include <limits.h>

/*@ predicate sorted(int* a, integer lo, integer hi) =
      \forall integer i, j; lo <= i <= j < hi ==> a[i] <= a[j];
*/

/* =========================================================================
 * SECTION 1: ARRAY PREDICATE FUNCTIONS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] >= 0;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] < 0;
*/
int all_nonnegative(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] >= 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < 0) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] <= 0;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] > 0;
*/
int all_nonpositive(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] <= 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > 0) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] == val;
    ensures \result == 0 ==>
        (n == 0 || \exists integer k; 0 <= k < n && a[k] != val);
*/
int all_equal_to(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != val) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] > val;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] <= val;
*/
int all_greater_than(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] > val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] <= val) return 0;
    }
    return 1;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n-1 ==> a[k] < a[k+1];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n-1 && a[k] >= a[k+1];
*/
int is_strictly_increasing(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n - 1;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] < a[k+1];
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        if (a[i] >= a[i + 1]) return 0;
    }
    return 1;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n-1 ==> a[k] > a[k+1];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n-1 && a[k] <= a[k+1];
*/
int is_strictly_decreasing(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n - 1;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] > a[k+1];
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        if (a[i] <= a[i + 1]) return 0;
    }
    return 1;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] == a[0];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] != a[0];
*/
int is_constant(const int *a, int n)
{
    int v = a[0];
    /*@ loop invariant 1 <= i <= n;
        loop invariant v == a[0];
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == v;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] != v) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires sorted(a, 0, n);
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer p, q; 0 <= p < q < n ==> a[p] < a[q];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n-1 && a[k] == a[k+1];
*/
int no_duplicates_sorted(const int *a, int n)
{
    if (n <= 1) return 1;
    /*@ loop invariant 0 <= i <= n - 1;
        loop invariant \forall integer p, q; 0 <= p < q <= i ==> a[p] < a[q];
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        if (a[i] == a[i + 1]) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> lo <= a[k] <= hi;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && (a[k] < lo || a[k] > hi);
*/
int all_in_bounds(const int *a, int n, int lo, int hi)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> lo <= a[k] <= hi;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < lo || a[i] > hi) return 0;
    }
    return 1;
}

/* =========================================================================
 * SECTION 2: COUNTING FUNCTIONS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_positive(const int *a, int n)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > 0) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_negative(const int *a, int n)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < 0) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_greater_than(const int *a, int n, int val)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > val) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_not_equal(const int *a, int n, int val)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != val) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_less_than(const int *a, int n, int val)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < val) cnt++;
    }
    return cnt;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n - 1;
*/
int count_sign_changes(const int *a, int n)
{
    int cnt = 0;
    /*@ loop invariant 1 <= i <= n;
        loop invariant 0 <= cnt <= i - 1;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if ((a[i - 1] > 0 && a[i] < 0) || (a[i - 1] < 0 && a[i] > 0))
            cnt++;
    }
    return cnt;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n - 1;
*/
int count_value_changes(const int *a, int n)
{
    int cnt = 0;
    /*@ loop invariant 1 <= i <= n;
        loop invariant 0 <= cnt <= i - 1;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] != a[i - 1]) cnt++;
    }
    return cnt;
}

/* =========================================================================
 * SECTION 3: SEARCH FUNCTIONS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] >= val;
    ensures \result >= 0 ==>
        \forall integer k; 0 <= k < \result ==> a[k] < val;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] < val;
*/
int find_first_ge(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] < val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] >= val) return i;
    }
    return -1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] <= val;
    ensures \result >= 0 ==>
        \forall integer k; 0 <= k < \result ==> a[k] > val;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] > val;
*/
int find_first_le(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] > val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] <= val) return i;
    }
    return -1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] == 0;
    ensures \result >= 0 ==>
        \forall integer k; 0 <= k < \result ==> a[k] != 0;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] != 0;
*/
int find_first_zero(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] != 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == 0) return i;
    }
    return -1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] < 0;
    ensures \result >= 0 ==>
        \forall integer k; 0 <= k < \result ==> a[k] >= 0;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] >= 0;
*/
int find_first_negative(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] >= 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < 0) return i;
    }
    return -1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] != val;
    ensures \result >= 0 ==>
        \forall integer k; 0 <= k < \result ==> a[k] == val;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] == val;
*/
int find_first_ne(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != val) return i;
    }
    return -1;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] > val;
    ensures \result >= 0 ==>
        \forall integer k; \result < k < n ==> a[k] <= val;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] <= val;
*/
int find_last_gt(const int *a, int n, int val)
{
    int result = -1;
    /*@ loop invariant 0 <= i <= n;
        loop invariant -1 <= result < i;
        loop invariant result >= 0 ==> a[result] > val;
        loop invariant result >= 0 ==>
            \forall integer k; result < k < i ==> a[k] <= val;
        loop invariant result == -1 ==>
            \forall integer k; 0 <= k < i ==> a[k] <= val;
        loop assigns i, result;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > val) result = i;
    }
    return result;
}

/* =========================================================================
 * SECTION 4: RANGE AND BOUNDED OPERATIONS (on int arrays)
 * ========================================================================= */

/*@ requires n >= 0;
    requires lo <= hi;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
    ensures \result < n ==> lo <= a[\result] <= hi;
    ensures \result < n ==>
        \forall integer k; 0 <= k < \result ==> !(lo <= a[k] <= hi);
    ensures \result == n ==>
        \forall integer k; 0 <= k < n ==> !(lo <= a[k] <= hi);
*/
int find_first_in_range(const int *a, int n, int lo, int hi)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> !(lo <= a[k] <= hi);
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] >= lo && a[i] <= hi) return i;
    }
    return n;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_outside_range(const int *a, int n, int lo, int hi)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < lo || a[i] > hi) cnt++;
    }
    return cnt;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n-1 ==> a[k] >= a[k+1];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n-1 && a[k] < a[k+1];
*/
int is_non_increasing(const int *a, int n)
{
    /*@ loop invariant 1 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i-1 ==> a[k] >= a[k+1];
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i - 1] < a[i]) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] < val;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] >= val;
*/
int all_less_than(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] < val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] >= val) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> !(lo <= a[k] <= hi);
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && lo <= a[k] <= hi;
*/
int none_in_range(const int *a, int n, int lo, int hi)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> !(lo <= a[k] <= hi);
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] >= lo && a[i] <= hi) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires lo <= hi;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] < lo ==> dst[k] == lo);
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] > hi ==> dst[k] == hi);
    ensures \forall integer k; 0 <= k < n ==>
        (lo <= src[k] <= hi ==> dst[k] == src[k]);
*/
void saturate_copy(const int *src, int *dst, int n, int lo, int hi)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] < lo ==> dst[k] == lo);
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] > hi ==> dst[k] == hi);
        loop invariant \forall integer k; 0 <= k < i ==>
            (lo <= src[k] <= hi ==> dst[k] == src[k]);
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (src[i] < lo)
            dst[i] = lo;
        else if (src[i] > hi)
            dst[i] = hi;
        else
            dst[i] = src[i];
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==>
        -1000000 <= src[k] <= 1000000;
    requires -1000 <= c <= 1000;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == src[k] + c;
*/
void shift_copy(const int *src, int *dst, int n, int c)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k] + c;
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = src[i] + c;
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==>
        -10000 <= src[k] <= 10000;
    requires -100 <= c <= 100;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == src[k] * c;
*/
void scale_copy(const int *src, int *dst, int n, int c)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k] * c;
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = src[i] * c;
    }
}

/* =========================================================================
 * SECTION 5: TWO-POINTER / PARTITIONING ALGORITHMS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] < pivot;
    ensures \forall integer k; \result <= k < n   ==> a[k] >= pivot;
*/
int partition(int *a, int n, int pivot)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] < pivot;
        loop invariant \forall integer k; j <= k < i ==> a[k] >= pivot;
        loop assigns i, j, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < pivot) {
            int tmp = a[j];
            a[j] = a[i];
            a[i] = tmp;
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] > val;
    ensures \forall integer k; \result <= k < n  ==> a[k] <= val;
*/
int segregate_greater(int *a, int n, int val)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] > val;
        loop invariant \forall integer k; j <= k < i ==> a[k] <= val;
        loop assigns i, j, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > val) {
            int tmp = a[j];
            a[j] = a[i];
            a[i] = tmp;
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] < 0;
    ensures \forall integer k; \result <= k < n  ==> a[k] >= 0;
*/
int segregate_negative(int *a, int n)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] < 0;
        loop invariant \forall integer k; j <= k < i ==> a[k] >= 0;
        loop assigns i, j, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < 0) {
            int tmp = a[j];
            a[j] = a[i];
            a[i] = tmp;
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] == 0;
    ensures \forall integer k; \result <= k < n  ==> a[k] != 0;
*/
int segregate_zeros(int *a, int n)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] == 0;
        loop invariant \forall integer k; j <= k < i ==> a[k] != 0;
        loop assigns i, j, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == 0) {
            int tmp = a[j];
            a[j] = a[i];
            a[i] = tmp;
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] <= pivot;
    ensures \forall integer k; \result <= k < n   ==> a[k] > pivot;
*/
int partition_le(int *a, int n, int pivot)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] <= pivot;
        loop invariant \forall integer k; j <= k < i ==> a[k] > pivot;
        loop assigns i, j, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] <= pivot) {
            int tmp = a[j];
            a[j] = a[i];
            a[i] = tmp;
            j++;
        }
    }
    return j;
}

/* =========================================================================
 * SECTION 6: ARRAY-TO-ARRAY TRANSFORM FUNCTIONS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(a + (0 .. n-1), dst + (0 .. n-1));
    requires \separated(b + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] >= b[k] ==> dst[k] == a[k]);
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] < b[k] ==> dst[k] == b[k]);
*/
void pointwise_max(const int *a, const int *b, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] >= b[k] ==> dst[k] == a[k]);
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] < b[k] ==> dst[k] == b[k]);
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = (a[i] >= b[i]) ? a[i] : b[i];
    }
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(a + (0 .. n-1), dst + (0 .. n-1));
    requires \separated(b + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] <= b[k] ==> dst[k] == a[k]);
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] > b[k] ==> dst[k] == b[k]);
*/
void pointwise_min(const int *a, const int *b, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] <= b[k] ==> dst[k] == a[k]);
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] > b[k] ==> dst[k] == b[k]);
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = (a[i] <= b[i]) ? a[i] : b[i];
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] >= threshold ==> dst[k] == 1);
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] < threshold ==> dst[k] == 0);
*/
void threshold_filter(const int *src, int *dst, int n, int threshold)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] >= threshold ==> dst[k] == 1);
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] < threshold ==> dst[k] == 0);
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = (src[i] >= threshold) ? 1 : 0;
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==>
        -46340 <= src[k] <= 46340;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == src[k] * src[k];
    ensures \forall integer k; 0 <= k < n ==> dst[k] >= 0;
*/
void map_square(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k] * src[k];
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] >= 0;
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = src[i] * src[i];
    }
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(a + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] > 0 ==> dst[k] == 1);
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] == 0 ==> dst[k] == 0);
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] < 0 ==> dst[k] == -1);
*/
void sign_array(const int *a, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] > 0 ==> dst[k] == 1);
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] == 0 ==> dst[k] == 0);
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] < 0 ==> dst[k] == -1);
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > 0)
            dst[i] = 1;
        else if (a[i] < 0)
            dst[i] = -1;
        else
            dst[i] = 0;
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] >= 0 ==> dst[k] == src[k]);
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] < 0 ==> dst[k] == 0);
    ensures \forall integer k; 0 <= k < n ==> dst[k] >= 0;
*/
void relu(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] >= 0 ==> dst[k] == src[k]);
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] < 0 ==> dst[k] == 0);
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] >= 0;
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = (src[i] >= 0) ? src[i] : 0;
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid_read(mask + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \separated(mask + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (mask[k] != 0 ==> dst[k] == src[k]);
    ensures \forall integer k; 0 <= k < n ==>
        (mask[k] == 0 ==> dst[k] == 0);
*/
void masked_copy(const int *src, const int *mask, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (mask[k] != 0 ==> dst[k] == src[k]);
        loop invariant \forall integer k; 0 <= k < i ==>
            (mask[k] == 0 ==> dst[k] == 0);
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = (mask[i] != 0) ? src[i] : 0;
    }
}

/* =========================================================================
 * SECTION 7: COMPACT / FILTER ALGORITHMS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> dst[k] > 0;
*/
int compact_positives(const int *src, int *dst, int n)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> dst[k] > 0;
        loop assigns i, j, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (src[i] > 0) {
            dst[j] = src[i];
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> dst[k] != 0;
*/
int compact_nonzero(const int *src, int *dst, int n)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> dst[k] != 0;
        loop assigns i, j, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (src[i] != 0) {
            dst[j] = src[i];
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> dst[k] > val;
*/
int compact_greater(const int *src, int *dst, int n, int val)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> dst[k] > val;
        loop assigns i, j, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (src[i] > val) {
            dst[j] = src[i];
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==>
        lo <= dst[k] <= hi;
*/
int compact_in_range(const int *src, int *dst, int n, int lo, int hi)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==>
            lo <= dst[k] <= hi;
        loop assigns i, j, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (src[i] >= lo && src[i] <= hi) {
            dst[j] = src[i];
            j++;
        }
    }
    return j;
}

/* =========================================================================
 * SECTION 8: MISCELLANEOUS VERIFIED ALGORITHMS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires sorted(a, 0, n);
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_distinct_sorted(const int *a, int n)
{
    if (n == 0) return 0;
    int cnt = 1;
    /*@ loop invariant 1 <= i <= n;
        loop invariant 1 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] != a[i - 1]) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    assigns \nothing;
    ensures \result >= 0;
    ensures \result <= n;
*/
int hamming_distance(const int *a, const int *b, int n)
{
    int d = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= d <= i;
        loop assigns i, d;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) d++;
    }
    return d;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result >= 0;
    ensures \result <= n;
*/
int longest_plateau(const int *a, int n)
{
    if (n == 0) return 0;
    int best = 1;
    int run = 1;
    /*@ loop invariant 1 <= i <= n;
        loop invariant 1 <= run <= i;
        loop invariant 1 <= best <= i;
        loop assigns i, run, best;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] == a[i - 1])
            run++;
        else
            run = 1;
        if (run > best) best = run;
    }
    return best;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_local_maxima(const int *a, int n)
{
    if (n <= 2) return 0;
    int cnt = 0;
    /*@ loop invariant 1 <= i <= n - 1;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - 1 - i;
    */
    for (int i = 1; i < n - 1; i++) {
        if (a[i] > a[i - 1] && a[i] > a[i + 1])
            cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_local_minima(const int *a, int n)
{
    if (n <= 2) return 0;
    int cnt = 0;
    /*@ loop invariant 1 <= i <= n - 1;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - 1 - i;
    */
    for (int i = 1; i < n - 1; i++) {
        if (a[i] < a[i - 1] && a[i] < a[i + 1])
            cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] <= b[k];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] > b[k];
*/
int pointwise_le(const int *a, const int *b, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] <= b[k];
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > b[i]) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(a + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] > hi && a[k] >= lo ==> dst[k] == 2);
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] < lo ==> dst[k] == 0);
    ensures \forall integer k; 0 <= k < n ==>
        (lo <= a[k] && a[k] <= hi ==> dst[k] == 1);
*/
void classify_range(const int *a, int *dst, int n, int lo, int hi)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] > hi && a[k] >= lo ==> dst[k] == 2);
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] < lo ==> dst[k] == 0);
        loop invariant \forall integer k; 0 <= k < i ==>
            (lo <= a[k] && a[k] <= hi ==> dst[k] == 1);
        loop invariant \forall integer k; 0 <= k < i ==>
            ((dst[k] == 0 ==> a[k] < lo) &&
            (dst[k] == 1 ==> lo <= a[k] <= hi) &&
            (dst[k] == 2 ==> a[k] > hi));
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < lo)
            dst[i] = 0;
        else if (a[i] > hi)
            dst[i] = 2;
        else
            dst[i] = 1;
    }
}

/*@ requires n > 0 && n <= INT_MAX;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result < n;
    ensures \forall integer k; 0 <= k < n ==> a[k] <= a[\result];
*/
int argmax(const int *a, int n)
{
    int idx = 0;
    /*@ loop invariant 1 <= i <= n;
        loop invariant 0 <= idx < i;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] <= a[idx];
        loop assigns i, idx;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] > a[idx]) idx = i;
    }
    return idx;
}

/*@ requires n > 0 && n <= INT_MAX;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result < n;
    ensures \forall integer k; 0 <= k < n ==> a[\result] <= a[k];
*/
int argmin(const int *a, int n)
{
    int idx = 0;
    /*@ loop invariant 1 <= i <= n;
        loop invariant 0 <= idx < i;
        loop invariant \forall integer k; 0 <= k < i ==> a[idx] <= a[k];
        loop assigns i, idx;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] < a[idx]) idx = i;
    }
    return idx;
}

/*@ requires n >= 1;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==>
        -1000000 <= src[k] <= 1000000;
    assigns dst[0 .. n-1];
    ensures dst[0] == src[0];
    ensures \forall integer k; 1 <= k < n ==> dst[k] == src[k] - src[k-1];
*/
void adjacent_difference(const int *src, int *dst, int n)
{
    dst[0] = src[0];
    /*@ loop invariant 1 <= i <= n;
        loop invariant dst[0] == src[0];
        loop invariant \forall integer k; 1 <= k < i ==> dst[k] == src[k] - src[k-1];
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        dst[i] = src[i] - src[i - 1];
    }
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    requires n <= 1000000;
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] == n - 1 - k;
*/
void fill_countdown(int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == n - 1 - k;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        a[i] = n - 1 - i;
    }
}

/*@ requires n >= 1;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n-1 ==>
        -1000000 <= src[k] + src[k+1] <= 1000000;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n-1 ==> dst[k] == src[k] + src[k+1];
    ensures dst[n-1] == src[n-1];
*/
void adjacent_sum_copy(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n-1;
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k] + src[k+1];
        loop assigns i, dst[0 .. n-1];
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        dst[i] = src[i] + src[i + 1];
    }
    dst[n - 1] = src[n - 1];
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] <= cap;
*/
void cap_at(int *a, int n, int cap)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] <= cap;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > cap) a[i] = cap;
    }
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] >= floor_val;
*/
void floor_at(int *a, int n, int floor_val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] >= floor_val;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < floor_val) a[i] = floor_val;
    }
}

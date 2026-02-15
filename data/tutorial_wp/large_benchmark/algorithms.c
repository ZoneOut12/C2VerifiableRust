/*****************************************************************************
 * Formally Verified Algorithms in C with ACSL Annotations
 *
 * Verify with: frama-c -wp -wp-rte algorithms.c
 *
 * No recursive, inductive, or axiomatic ACSL definitions are used.
 *****************************************************************************/

#include <limits.h>

/*@ predicate sorted(int* a, integer lo, integer hi) =
      \forall integer i, j; lo <= i <= j < hi ==> a[i] <= a[j];
*/

/* =========================================================================
 * SECTION 1: BASIC UTILITY FUNCTIONS
 * ========================================================================= */

/*@ requires \valid(a) && \valid(b);
    requires \separated(a, b);
    assigns *a, *b;
    ensures *a == \old(*b);
    ensures *b == \old(*a);
*/
void swap(int *a, int *b)
{
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@ requires v > INT_MIN;
    assigns \nothing;
    ensures \result >= 0;
    ensures v >= 0 ==> \result == v;
    ensures v <  0 ==> \result == -v;
*/
int abs_val(int v)
{
    return v >= 0 ? v : -v;
}

/*@ assigns \nothing;
    ensures \result >= a && \result >= b;
    ensures \result == a || \result == b;
*/
int max_int(int a, int b)
{
    return a >= b ? a : b;
}

/*@ assigns \nothing;
    ensures \result <= a && \result <= b;
    ensures \result == a || \result == b;
*/
int min_int(int a, int b)
{
    return a <= b ? a : b;
}

/*@ requires lo <= hi;
    assigns \nothing;
    ensures lo <= \result <= hi;
    ensures v < lo       ==> \result == lo;
    ensures v > hi       ==> \result == hi;
    ensures lo <= v <= hi ==> \result == v;
*/
int clamp(int v, int lo, int hi)
{
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}

/*@ assigns \nothing;
    ensures \result >= a && \result >= b && \result >= c;
    ensures \result == a || \result == b || \result == c;
*/
int max3(int a, int b, int c)
{
    int m = a;
    if (b > m) m = b;
    if (c > m) m = c;
    return m;
}

/*@ assigns \nothing;
    ensures (v > 0 ==> \result ==  1);
    ensures (v == 0 ==> \result == 0);
    ensures (v < 0 ==> \result == -1);
*/
int sign(int v)
{
    if (v > 0) return 1;
    if (v < 0) return -1;
    return 0;
}

/* =========================================================================
 * SECTION 2: ARRAY QUERY FUNCTIONS
 * ========================================================================= */

/*@ requires n > 0 && n <= INT_MAX;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \forall integer k; 0 <= k < n ==> \result <= a[k];
    ensures \exists integer k; 0 <= k < n && a[k] == \result;
*/
int array_min(const int *a, int n)
{
    int m = a[0];
    /*@ loop invariant 1 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> m <= a[k];
        loop invariant \exists integer k; 0 <= k < i && a[k] == m;
        loop assigns i, m;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] < m) m = a[i];
    }
    return m;
}

/*@ requires n > 0 && n <= INT_MAX;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result < n;
    ensures \forall integer k; 0 <= k < n ==> a[k] <= a[\result];
*/
int array_max_index(const int *a, int n)
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
int array_min_index(const int *a, int n)
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

/*@ requires n >= 0 && n <= 100000;
    requires \valid_read(a + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==> -10000 <= a[k] <= 10000;
    assigns \nothing;
    ensures -10000 * n <= \result <= 10000 * n;
*/
int array_sum(const int *a, int n)
{
    int s = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant -10000 * i <= s <= 10000 * i;
        loop assigns i, s;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        s += a[i];
    }
    return s;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < n ==>
        (a[k] == val ==> \result > 0);
*/
int array_count(const int *a, int n, int val)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop invariant \forall integer k; 0 <= k < i ==>
            (a[k] == val ==> cnt > 0);
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == val) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires lo <= hi;
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int array_count_in_range(const int *a, int n, int lo, int hi)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop invariant \forall integer k; 0 <= k < i ==>
            (lo <= a[k] <= hi  ==> cnt > 0);
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] >= lo && a[i] <= hi) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> lo <= a[k] <= hi;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && (a[k] < lo || a[k] > hi);
    ensures \result == 0 || \result == 1;
*/
int all_in_range(const int *a, int n, int lo, int hi)
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

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] > 0;
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] <= 0;
    ensures \result == 0 || \result == 1;
*/
int all_positive(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] > 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] <= 0) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 1 ==>
        \exists integer k; 0 <= k < n && a[k] == 0;
    ensures \result == 0 ==>
        \forall integer k; 0 <= k < n ==> a[k] != 0;
    ensures \result == 0 || \result == 1;
*/
int any_zero(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] != 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == 0) return 1;
    }
    return 0;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 1 ==> sorted(a, 0, n);
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n-1 && a[k] > a[k+1];
    ensures \result == 0 || \result == 1;
*/
int is_sorted_check(const int *a, int n)
{
    if (n <= 1) return 1;
    /*@ loop invariant 0 <= i <= n - 1;
        loop invariant \forall integer p, q;
            0 <= p <= q <= i ==> a[p] <= a[q];
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        if (a[i] > a[i + 1]) return 0;
    }
    return 1;
}

/* =========================================================================
 * SECTION 3: ARRAY COMPARISON FUNCTIONS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    assigns \nothing;
    ensures \result == 1 ==>
        \forall integer k; 0 <= k < n ==> a[k] == b[k];
    ensures \result == 0 ==>
        \exists integer k; 0 <= k < n && a[k] != b[k];
    ensures \result == 0 || \result == 1;
*/
int array_equal(const int *a, const int *b, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == b[k];
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] == b[k];
    ensures \result < n ==> a[\result] != b[\result];
*/
int mismatch(const int *a, const int *b, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == b[k];
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) return i;
    }
    return n;
}

/*@ requires n >= 1;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n - 1;
    ensures \result >= 0 ==> a[\result] == a[\result + 1];
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n-1 ==> a[k] != a[k+1];
*/
int adjacent_find(const int *a, int n)
{
    if (n <= 1) return -1;
    /*@ loop invariant 0 <= i <= n - 1;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] != a[k+1];
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        if (a[i] == a[i + 1]) return i;
    }
    return -1;
}

/* =========================================================================
 * SECTION 4: SEARCH ALGORITHMS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] == val;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] != val;
*/
int linear_search(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] != val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == val) return i;
    }
    return -1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] == val;
    ensures \result >= 0 ==>
        \forall integer k; \result < k < n ==> a[k] != val;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] != val;
*/
int find_last(const int *a, int n, int val)
{
    int result = -1;
    /*@ loop invariant 0 <= i <= n;
        loop invariant -1 <= result < i;
        loop invariant result >= 0 ==> a[result] == val;
        loop invariant result >= 0 ==>
            \forall integer k; result < k < i ==> a[k] != val;
        loop invariant result == -1 ==>
            \forall integer k; 0 <= k < i ==> a[k] != val;
        loop assigns i, result;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == val) result = i;
    }
    return result;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==> a[\result] > 0;
    ensures \result >= 0 ==>
        \forall integer k; 0 <= k < \result ==> a[k] <= 0;
    ensures \result == -1 ==>
        \forall integer k; 0 <= k < n ==> a[k] <= 0;
*/
int find_first_positive(const int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] <= 0;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] > 0) return i;
    }
    return -1;
}

/*@ requires n >= 3;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==>
        (1 <= \result <= n-2 && 
         a[\result] > a[\result-1] && 
         a[\result] > a[\result+1]);
    ensures \result == -1 ==>
        \forall integer k; 1 <= k <= n-2 ==>
            (a[k] <= a[k-1] || a[k] <= a[k+1]);
*/
int find_peak(const int *a, int n)
{
    /*@ loop invariant 1 <= i <= n - 1;
        loop invariant \forall integer k; 1 <= k < i ==>
            (a[k] <= a[k-1] || a[k] <= a[k+1]);
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 1; i < n - 1; i++) {
        if (a[i] > a[i - 1] && a[i] > a[i + 1]) {
            return i;
        }
    }
    return -1;
}

/*@ requires n >= 3;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures -1 <= \result < n;
    ensures \result >= 0 ==>
        (1 <= \result <= n-2 && 
         a[\result] < a[\result-1] && 
         a[\result] < a[\result+1]);
    ensures \result == -1 ==>
        \forall integer k; 1 <= k <= n-2 ==>
            (a[k] >= a[k-1] || a[k] >= a[k+1]);
*/
int find_valley(const int *a, int n)
{
    /*@ loop invariant 1 <= i <= n - 1;
        loop invariant \forall integer k; 1 <= k < i ==>
            (a[k] >= a[k-1] || a[k] >= a[k+1]);
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 1; i < n - 1; i++) {
        if (a[i] < a[i - 1] && a[i] < a[i + 1]) {
            return i;
        }
    }
    return -1;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
    ensures n > 0 ==> \result >= 1;
*/
int max_increasing_length(const int *a, int n)
{
    if (n == 0) return 0;
    
    int max_len = 1;
    int cur_len = 1;
    
    /*@ loop invariant 1 <= i <= n;
        loop invariant 1 <= cur_len <= i;
        loop invariant 1 <= max_len <= i;
        loop invariant max_len >= cur_len;
        loop assigns i, cur_len, max_len;
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        if (a[i] > a[i - 1]) {
            cur_len++;
            if (cur_len > max_len) {
                max_len = cur_len;
            }
        } else {
            cur_len = 1;
        }
    }
    return max_len;
}

/* =========================================================================
 * SECTION 5: ARRAY TRANSFORMATION FUNCTIONS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] == val;
*/
void array_fill(int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == val;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        a[i] = val;
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == src[k];
*/
void array_copy(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] == src[k];
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = src[i];
    }
}

/*@ requires n >= 0 && n <= INT_MAX;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] == k;
*/
void array_init_iota(int *a, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] == k;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        a[i] = i;
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==>
        INT_MIN <= src[k] + c && src[k] + c <= INT_MAX;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == src[k] + c;
*/
void array_add_scalar(const int *src, int *dst, int n, int c)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            dst[k] == src[k] + c;
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
    requires \forall integer k; 0 <= k < n ==> src[k] > INT_MIN;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == -src[k];
*/
void array_negate(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            dst[k] == -src[k];
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = -src[i];
    }
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    requires old_val != new_val;
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> a[k] != old_val;
*/
void array_replace(int *a, int n, int old_val, int new_val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] != old_val;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == old_val) a[i] = new_val;
    }
}

/*@ requires n > 0 && n <= 10000;
    requires \valid_read(a + (0 .. n-1));
    requires \valid(out + (0 .. n-1));
    requires \separated(a + (0 .. n-1), out + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==> -100000 <= a[k] <= 100000;
    assigns out[0 .. n-1];
    ensures out[0] == a[0];
    ensures \forall integer k; 1 <= k < n ==> out[k] == out[k-1] + a[k];
*/
void prefix_sum(const int *a, int *out, int n)
{
    out[0] = a[0];
    /*@ loop invariant 1 <= i <= n;
        loop invariant out[0] == a[0];
        loop invariant \forall integer k; 1 <= k < i ==>
            out[k] == out[k-1] + a[k];
        loop invariant -100000 * i <= out[i-1] <= 100000 * i;
        loop assigns i, out[1 .. n-1];
        loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        out[i] = out[i - 1] + a[i];
    }
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> dst[k] == src[n-1-k];
*/
void array_reverse_copy(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            dst[k] == src[n-1-k];
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dst[i] = src[n - 1 - i];
    }
}

/* =========================================================================
 * SECTION 6: ADVANCED ARRAY ALGORITHMS
 * ========================================================================= */

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \exists integer k; 0 <= k < n && a[k] == val;
    ensures \result == 0 ==>
        \forall integer k; 0 <= k < n ==> a[k] != val;
*/
int array_contains(const int *a, int n, int val)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] != val;
        loop assigns i;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == val) return 1;
    }
    return 0;
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] != val;
*/
int remove_element(int *a, int n, int val)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] != val;
        loop assigns i, j, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != val) {
            a[j] = a[i];
            j++;
        }
    }
    return j;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result <= n;
*/
int count_zeros(const int *a, int n)
{
    int cnt = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= cnt <= i;
        loop assigns i, cnt;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] == 0) cnt++;
    }
    return cnt;
}

/*@ requires n >= 0 && n <= 10000;
    requires \valid_read(a + (0 .. n-1));
    requires \valid_read(b + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==> 0 <= a[k] <= 100;
    requires \forall integer k; 0 <= k < n ==> 0 <= b[k] <= 100;
    assigns \nothing;
    ensures 0 <= \result <= 10000 * n;
*/
int inner_product(const int *a, const int *b, int n)
{
    int s = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= s <= 10000 * i;
        loop assigns i, s;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        //@ assert 0 <= a[i] * b[i] <= 10000;
        s += a[i] * b[i];
    }
    return s;
}

/*@ requires 0 < lo < hi;
    requires \valid_read(a + (lo .. hi - 1));
    assigns \nothing;
    ensures lo <= \result < hi;
    ensures \forall integer k; lo <= k < hi ==> a[\result] <= a[k];
*/
int find_min_in_range(const int *a, int lo, int hi)
{
    int idx = lo;
    /*@ loop invariant lo + 1 <= i <= hi;
        loop invariant lo <= idx < i;
        loop invariant \forall integer k; lo <= k < i ==> a[idx] <= a[k];
        loop assigns i, idx;
        loop variant hi - i;
    */
    for (int i = lo + 1; i < hi; i++) {
        if (a[i] < a[idx]) idx = i;
    }
    return idx;
}

/*@ requires n >= 2;
    requires \valid_read(a + (0 .. n-1));
    assigns \nothing;
    ensures 0 <= \result < n;
    ensures \exists integer k; 0 <= k < n && k != \result && a[k] >= a[\result];
*/
int find_second_max_index(const int *a, int n)
{
    int first, second;
    if (a[0] >= a[1]) {
        first = 0; second = 1;
    } else {
        first = 1; second = 0;
    }
    /*@ loop invariant 2 <= i <= n;
        loop invariant 0 <= first < i && 0 <= second < i;
        loop invariant first != second;
        loop invariant \forall integer k; 0 <= k < i ==> a[k] <= a[first];
        loop invariant \forall integer k; 0 <= k < i && k != first ==>
            a[k] <= a[second];
        loop assigns i, first, second;
        loop variant n - i;
    */
    for (int i = 2; i < n; i++) {
        if (a[i] > a[first]) {
            second = first;
            first = i;
        } else if (a[i] > a[second]) {
            second = i;
        }
    }
    return second;
}

/*@ requires n >= 0;
    requires \valid_read(a + (0 .. n-1));
    requires sorted(a, 0, n);
    assigns \nothing;
    ensures \result == 0 || \result == 1;
    ensures \result == 1 ==>
        \forall integer p, q; 0 <= p < q < n ==> a[p] < a[q];
    ensures \result == 0 ==>
        (n >= 2 && \exists integer k; 0 <= k < n-1 && a[k] == a[k+1]);
*/
int all_distinct_sorted(const int *a, int n)
{
    if (n <= 1) return 1;
    /*@ loop invariant 0 <= i <= n - 1;
        loop invariant \forall integer p, q;
            0 <= p < q <= i ==> a[p] < a[q];
        loop assigns i;
        loop variant n - 1 - i;
    */
    for (int i = 0; i < n - 1; i++) {
        if (a[i] == a[i + 1]) return 0;
    }
    return 1;
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==>
        a[k] == 0 || a[k] == 1;
    assigns a[0 .. n-1];
    ensures 0 <= \result <= n;
    ensures \forall integer k; 0 <= k < \result ==> a[k] == 0;
    ensures \forall integer k; \result <= k < n  ==> a[k] == 1;
*/
int partition_binary(int *a, int n)
{
    int j = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= j <= i;
        loop invariant \forall integer k; 0 <= k < j ==> a[k] == 0;
        loop invariant \forall integer k; j <= k < i ==> a[k] == 1;
        loop invariant \forall integer k; i <= k < n ==>
            (a[k] == 0 || a[k] == 1);
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
    requires \valid_read(a + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==> 0 <= a[k] <= 10000;
    requires n <= 10000;
    assigns \nothing;
    ensures 0 <= \result;
*/
int max_prefix_sum(const int *a, int n)
{
    int current = 0;
    int best = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant 0 <= current <= 10000 * i;
        loop invariant 0 <= best <= 10000 * i;
        loop invariant best >= current || best >= 0;
        loop assigns i, current, best;
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        current += a[i];
        if (current > best) best = current;
    }
    return best;
}

/*@ requires n >= 0;
    requires \valid_read(src + (0 .. n-1));
    requires \valid(dst + (0 .. n-1));
    requires \separated(src + (0 .. n-1), dst + (0 .. n-1));
    requires \forall integer k; 0 <= k < n ==> src[k] > INT_MIN;
    assigns dst[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] >= 0 ==> dst[k] == src[k]);
    ensures \forall integer k; 0 <= k < n ==>
        (src[k] < 0  ==> dst[k] == -src[k]);
    ensures \forall integer k; 0 <= k < n ==> dst[k] >= 0;
*/
void array_map_abs(const int *src, int *dst, int n)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] >= 0 ==> dst[k] == src[k]);
        loop invariant \forall integer k; 0 <= k < i ==>
            (src[k] < 0  ==> dst[k] == -src[k]);
        loop invariant \forall integer k; 0 <= k < i ==> dst[k] >= 0;
        loop assigns i, dst[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (src[i] >= 0)
            dst[i] = src[i];
        else
            dst[i] = -src[i];
    }
}

/*@ requires n >= 0;
    requires \valid(a + (0 .. n-1));
    requires lo <= hi;
    assigns a[0 .. n-1];
    ensures \forall integer k; 0 <= k < n ==> lo <= a[k] <= hi;
*/
void array_clamp_all(int *a, int n, int lo, int hi)
{
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> lo <= a[k] <= hi;
        loop assigns i, a[0 .. n-1];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] < lo) a[i] = lo;
        else if (a[i] > hi) a[i] = hi;
    }
}

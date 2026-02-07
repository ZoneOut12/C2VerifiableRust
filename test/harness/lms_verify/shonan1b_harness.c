/*@
logic boolean row_col_bool(integer c, int r, int n, int* m, int* v) =
  (0 < c <= n) ? ((row_col_bool(c-1, r, n, m, v)) || (m[n*r+(c-1)] && v[(c-1)])) : 0;
 */

/*@
requires n>0;
requires n<3;

requires \valid(m+(0..n*n-1));
requires \valid(v+(0..n-1));
requires \valid(o+(0..n-1));
requires \separated(m+(0..n*n-1), v+(0..n-1), o+(0..n-1));

assigns o[0..n-1];

ensures \forall int i; 0 <= i < n ==>
  o[i] == row_col_bool(n, i, n, m, v);
*/
void mv_mult_bool(int n, int *m, int *v, int *o) {
  /*@
    loop invariant 0 <= r <= n;
    loop invariant \forall int i; 0 <= i < r ==> o[i] == row_col_bool(n, i, n, m, v);
    loop assigns r, o[0..n-1];
    loop variant n-r;
   */
  for (int r = 0; r < n; r++) {
    o[r] = 0;
    /*@
      loop invariant 0 <= c <= n;
      loop invariant 0 <= r < n;
      loop invariant \forall int i; 0 <= i < r ==> o[i] == row_col_bool(n, i, n, m, v);
      loop invariant o[r] == row_col_bool(c, r, n, m, v);
      loop assigns c, o[r];
      loop variant n-c;
    */
    for (int c = 0; c < n; c++) {
      o[r] = o[r] || (m[n*r+c] && v[c]);
    }
  }
}


/*@
requires n>0;
requires n==2;

requires \valid(m+(0..n*n-1));
requires \valid(v+(0..n-1));
requires \valid(o+(0..n-1));
requires \separated(m+(0..n*n-1), v+(0..n-1), o+(0..n-1));

requires m[0]==1;
requires m[1]==1;
requires m[2]==0;
requires m[3]==0;

assigns o[0..n-1];

ensures \forall int i; 0 <= i < n ==>
  o[i] == row_col_bool(n, i, n, m, v);
*/
void mv_mults_bool(int n, int *m, int *v, int *o) {
  int r = 0;
  o[r] = 0;
  /*@
    loop invariant 0 <= c <= n;
    loop invariant 0 <= r < n;
    loop invariant \forall int i; 0 <= i < r ==> o[i] == row_col_bool(n, i, n, m, v);
    loop invariant o[r] == row_col_bool(c, r, n, m, v);
    loop assigns c, o[r];
    loop variant n-c;
  */
  for (int c = 0; c < n; c++) {
    o[r] = o[r] || (m[n*r+c] && v[c]);
  }
  o[1] = 0;
}


/*@
requires n>0;
requires n==2;

requires \valid(m+(0..n*n-1));
requires \valid(v+(0..n-1));
requires \valid(o+(0..n-1));
requires \separated(m+(0..n*n-1), v+(0..n-1), o+(0..n-1));

requires m[0]==1;
requires m[1]==1;
requires m[2]==0;
requires m[3]==0;

assigns o[0..n-1];

ensures \forall int i; 0 <= i < n ==>
  o[i] == row_col_bool(n, i, n, m, v);
*/
void mv_multu_bool(int n, int *m, int *v, int *o) {
  o[0] = 0;
  o[0] = o[0] || v[0];
  o[0] = o[0] || v[1];
  o[1] = 0;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <assert.h>

void test_mv_mult_bool() {
    int o[2];

    // --- 7 Valid Cases ---
    // 1. n=2, Identity
    int m1[] = {1,0,0,1}, v1[] = {1,1}; mv_mult_bool(2, m1, v1, o); 
    assert(o[0] == 1 && o[1] == 1);

    // 2. n=2, All Zeros
    int m2[] = {0,0,0,0}, v2[] = {1,1}; mv_mult_bool(2, m2, v2, o); 
    assert(o[0] == 0 && o[1] == 0);

    // 3. n=2, All Ones
    int m3[] = {1,1,1,1}, v3[] = {1,1}; mv_mult_bool(2, m3, v3, o); 
    assert(o[0] == 1 && o[1] == 1);

    // 4. n=1, Single Element
    int m4[] = {1}, v4[] = {1}; mv_mult_bool(1, m4, v4, o); 
    assert(o[0] == 1);

    // 5. n=2, Sparse Row
    int m5[] = {0,1,1,0}, v5[] = {0,1}; mv_mult_bool(2, m5, v5, o); 
    assert(o[0] == 1 && o[1] == 0);

    // 6. n=2, Zero Vector
    int m6[] = {1,1,1,1}, v6[] = {0,0}; mv_mult_bool(2, m6, v6, o); 
    assert(o[0] == 0 && o[1] == 0);

    // 7. n=2, Diagonal Swap
    int m7[] = {0,1,1,0}, v7[] = {1,0}; mv_mult_bool(2, m7, v7, o); 
    assert(o[0] == 0 && o[1] == 1);

    // --- 2 Invalid Cases (Triggered via manual checks or ACSL) ---
    // 8. Violation: n out of bounds (n=3)
    // mv_mult_bool(3, m1, v1, o); 

    // 9. Violation: Buffer too short for n=2
    // int m_short[] = {1,0}; mv_mult_bool(2, m_short, v1, o);
}

void test_mv_mults_bool() {
    int o[2];
    int ms[] = {1,1,0,0}; // Required matrix

    // --- 7 Valid Cases ---
    // 1. Both v inputs true
    int v1[] = {1,1}; mv_mults_bool(2, ms, v1, o); assert(o[0] == 1 && o[1] == 0);
    // 2. All v inputs false
    int v2[] = {0,0}; mv_mults_bool(2, ms, v2, o); assert(o[0] == 0 && o[1] == 0);
    // 3. First v input true
    int v3[] = {1,0}; mv_mults_bool(2, ms, v3, o); assert(o[0] == 1 && o[1] == 0);
    // 4. Second v input true
    int v4[] = {0,1}; mv_mults_bool(2, ms, v4, o); assert(o[0] == 1 && o[1] == 0);
    // 5. Truth-value (non-zero is true)
    int v5[] = {5,0}; mv_mults_bool(2, ms, v5, o); assert(o[0] == 1 && o[1] == 0);
    // 6. Repetition check
    int v6[] = {1,1}; mv_mults_bool(2, ms, v6, o); assert(o[0] == 1 && o[1] == 0);
    // 7. Repetition check
    int v7[] = {0,0}; mv_mults_bool(2, ms, v7, o); assert(o[0] == 0 && o[1] == 0);

    // --- 2 Invalid Cases ---
    // 8. Violation: Wrong matrix content
    int m_bad[] = {0,0,1,1}; 
    // mv_mults_bool(2, m_bad, v1, o);

    // 9. Violation: n mismatch (n=1)
    // mv_mults_bool(1, ms, v1, o);
}

void test_mv_multu_bool() {
    int o[2];
    int ms[] = {1,1,0,0};

    // --- 7 Valid Cases ---
    // 1. Standard full
    int v1[] = {1,1}; mv_multu_bool(2, ms, v1, o); assert(o[0] == 1 && o[1] == 0);
    // 2. Only first
    int v2[] = {1,0}; mv_multu_bool(2, ms, v2, o); assert(o[0] == 1 && o[1] == 0);
    // 3. Only second
    int v3[] = {0,1}; mv_multu_bool(2, ms, v3, o); assert(o[0] == 1 && o[1] == 0);
    // 4. None
    int v4[] = {0,0}; mv_multu_bool(2, ms, v4, o); assert(o[0] == 0 && o[1] == 0);
    // 5. Large value check
    int v5[] = {10,20}; mv_multu_bool(2, ms, v5, o); assert(o[0] == 1 && o[1] == 0);
    // 6. Signed check (non-zero)
    int v6[] = {-1,0}; mv_multu_bool(2, ms, v6, o); assert(o[0] == 1 && o[1] == 0);
    // 7. Zero vector
    int v7[] = {0,0}; mv_multu_bool(2, ms, v7, o); assert(o[0] == 0 && o[1] == 0);

    // --- 2 Invalid Cases ---
    // 8. Violation: Matrix content requirement (requires m[0]==1 etc.)
    int m_fail[] = {1,0,1,0};
    // mv_multu_bool(2, m_fail, v1, o);

    // 9. Violation: Buffer overlap (separated requirement)
    // mv_multu_bool(2, ms, v1, v1); 
}
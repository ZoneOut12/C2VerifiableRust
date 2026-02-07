// ========== Original Code (with ACSL) ==========
/*@
requires \valid_read(m+(0..3));
requires \valid_read(v+(0..1));
requires \valid(o+(0..1));
requires \forall int i; \forall int j;
  0 <= i < 4 && 0 <= j < 2 ==> \separated(m+i,o+j);
requires \forall int i; \forall int j;
  0 <= i < 2 && 0 <= j < 2 ==> \separated(v+i,o+j);

assigns o[0..1];

ensures o[0] == (m[0] && v[0]) || (m[1] && v[1]);
ensures o[1] == (m[2] && v[0]) || (m[3] && v[1]);
*/
void mv_mult2_bool(int *m, int *v, int *o) {
  o[0] = (m[0] && v[0]) || (m[1] && v[1]);
  o[1] = (m[2] && v[0]) || (m[3] && v[1]);
}

/*@
requires \valid_read(m+(0..3));
requires \valid_read(v+(0..1));
requires \valid(o+(0..1));
requires \forall int i; \forall int j;
  0 <= i < 4 && 0 <= j < 2 ==> \separated(m+i,o+j);
requires \forall int i; \forall int j;
  0 <= i < 2 && 0 <= j < 2 ==> \separated(v+i,o+j);

requires \forall int i; 0 <= i < 4 ==> 0 <= m[i] <= 1;
requires \forall int i; 0 <= i < 2 ==> 0 <= v[i] <= 1;

assigns o[0..1];

ensures o[0] == m[0]*v[0]+m[1]*v[1];
ensures o[1] == m[2]*v[0]+m[3]*v[1];
*/
void mv_mult2(int *m, int *v, int *o) {
  o[0] = m[0]*v[0]+m[1]*v[1];
  o[1] = m[2]*v[0]+m[3]*v[1];
}

/*@
requires n==2;

requires \valid_read(m+(0..n*n-1));
requires \valid_read(v+(0..n-1));
requires \valid(o+(0..n-1));
requires \forall int i; \forall int j;
  0 <= i < n*n && 0 <= j < n ==> \separated(m+i,o+j);
requires \forall int i; \forall int j;
  0 <= i < n && 0 <= j < n ==> \separated(v+i,o+j);

assigns o[0..n-1];

ensures \forall int i; 0 <= i < n ==> o[i] == (m[n*i+0] && v[0]) || (m[n*i+1] && v[1]);
*/
void mv_mult2r_bool(int n, int *m, int *v, int *o) {
  /*@
    loop invariant 0 <= r <= n;
    loop invariant \forall int i; 0 <= i < r ==> o[i] == (m[n*i+0] && v[0]) || (m[n*i+1] && v[1]);
    loop assigns r, o[0..n-1];
    loop variant n-r;
   */
  for (int r = 0; r < n; r++) {
    int t = 0;
    /*@
      loop invariant 0 <= c <= n;
      loop invariant t == ((c==0) ? 0 : ((m[n*r+0] && v[0]) || ((c==1)? 0 : (m[n*r+1] && v[1]))));
      loop assigns c, t;
      loop variant n-c;
    */
    for (int c = 0; c < n; c++) {
      t = t || (m[n*r+c] && v[c]);
    }
    o[r] = t;
  }
}

/*@
requires n==2;

requires \valid_read(m+(0..n*n-1));
requires \valid_read(v+(0..n-1));
requires \valid(o+(0..n-1));
requires \forall int i; \forall int j;
  0 <= i < n*n && 0 <= j < n ==> \separated(m+i,o+j);
requires \forall int i; \forall int j;
  0 <= i < n && 0 <= j < n ==> \separated(v+i,o+j);

requires m[0]==1;
requires m[1]==1;
requires m[2]==0;
requires m[3]==0;

assigns o[0..n-1];

ensures \forall int i; 0 <= i < n ==> o[i] == (m[n*i+0] && v[0]) || (m[n*i+1] && v[1]);
*/
void mv_mult2s_bool(int n, int *m, int *v, int *o) {
  int r = 0;
  int t = 0;
  /*@
    loop invariant 0 <= c <= n;
    loop invariant t == ((c==0) ? 0 : ((m[n*r+0] && v[0]) || ((c==1)? 0 : (m[n*r+1] && v[1]))));
    loop assigns c, t;
    loop variant n-c;
  */
  for (int c = 0; c < n; c++) {
    t = t || (m[n*r+c] && v[c]);
  }
  o[r] = t;
  o[1] = 0;
}
 
// ========== Test Cases ==========

void test_harness_mv_mult2_bool() {
    int o[2];
    // --- 7 Valid Cases ---
    int m1[] = {1,0,0,1}, v1[] = {1,1}; mv_mult2_bool(m1, v1, o); assert(o[0]==1 && o[1]==1);
    int m2[] = {0,0,0,0}, v2[] = {1,1}; mv_mult2_bool(m2, v2, o); assert(o[0]==0 && o[1]==0);
    int m3[] = {1,1,1,1}, v3[] = {0,0}; mv_mult2_bool(m3, v3, o); assert(o[0]==0 && o[1]==0);
    int m4[] = {1,1,0,0}, v4[] = {1,0}; mv_mult2_bool(m4, v4, o); assert(o[0]==1 && o[1]==0);
    int m5[] = {0,0,1,1}, v5[] = {0,1}; mv_mult2_bool(m5, v5, o); assert(o[0]==0 && o[1]==1);
    int m6[] = {1,1,1,1}, v6[] = {1,1}; mv_mult2_bool(m6, v6, o); assert(o[0]==1 && o[1]==1);
    int m7[] = {0,1,1,0}, v7[] = {1,0}; mv_mult2_bool(m7, v7, o); assert(o[0]==0 && o[1]==1);

    // --- 2 Invalid Cases ---
    // 8. NULL pointer: mv_mult2_bool(NULL, v1, o);
    // 9. Aliasing: mv_mult2_bool(m1, v1, m1);
}

void test_harness_mv_mult2() {
    int o[2];
    // --- 7 Valid Cases ---
    int m1[] = {1,0,0,1}, v1[] = {1,1}; mv_mult2(m1, v1, o); assert(o[0]==1 && o[1]==1);
    int m2[] = {1,1,1,1}, v2[] = {1,1}; mv_mult2(m2, v2, o); assert(o[0]==2 && o[1]==2); // Arithmetic sum
    int m3[] = {0,0,0,0}, v3[] = {1,1}; mv_mult2(m3, v3, o); assert(o[0]==0 && o[1]==0);
    int m4[] = {1,1,0,0}, v4[] = {1,1}; mv_mult2(m4, v4, o); assert(o[0]==2 && o[1]==0);
    int m5[] = {0,1,0,1}, v5[] = {1,1}; mv_mult2(m5, v5, o); assert(o[0]==1 && o[1]==1);
    int m6[] = {1,0,1,0}, v6[] = {1,0}; mv_mult2(m6, v6, o); assert(o[0]==1 && o[1]==1);
    int m7[] = {1,1,1,1}, v7[] = {0,0}; mv_mult2(m7, v7, o); assert(o[0]==0 && o[1]==0);

    // --- 2 Invalid Cases ---
    // 8. Non-binary input: int mb[]={2,0,0,0}; mv_mult2(mb, v1, o);
    // 9. NULL pointer: mv_mult2(m1, NULL, o);
}

void test_harness_mv_mult2r_bool() {
    int o[2];
    // --- 7 Valid Cases ---
    int m1[] = {1,0,0,1}, v1[] = {1,1}; mv_mult2r_bool(2, m1, v1, o); assert(o[0]==1 && o[1]==1);
    int m2[] = {0,1,1,0}, v2[] = {1,1}; mv_mult2r_bool(2, m2, v2, o); assert(o[0]==1 && o[1]==1);
    int m3[] = {0,0,0,0}, v3[] = {1,1}; mv_mult2r_bool(2, m3, v3, o); assert(o[0]==0 && o[1]==0);
    int m4[] = {1,1,1,1}, v4[] = {0,1}; mv_mult2r_bool(2, m4, v4, o); assert(o[0]==1 && o[1]==1);
    int m5[] = {1,0,1,0}, v5[] = {0,1}; mv_mult2r_bool(2, m5, v5, o); assert(o[0]==0 && o[1]==0);
    int m6[] = {1,1,0,0}, v6[] = {0,0}; mv_mult2r_bool(2, m6, v6, o); assert(o[0]==0 && o[1]==0);
    int m7[] = {1,0,0,1}, v7[] = {1,0}; mv_mult2r_bool(2, m7, v7, o); assert(o[0]==1 && o[1]==0);

    // --- 2 Invalid Cases ---
    // 8. Wrong n: mv_mult2r_bool(3, m1, v1, o); // n must be 2
    // 9. Aliasing: mv_mult2r_bool(2, m1, o, o); // v and o overlap
}

void test_harness_mv_mult2s_bool() {
    int o[2];
    int ms[] = {1,1,0,0}; // The only matrix allowed by 'requires'

    // --- 7 Valid Cases (Varying Vector) ---
    int v1[] = {1,1}; mv_mult2s_bool(2, ms, v1, o); assert(o[0]==1 && o[1]==0);
    int v2[] = {1,0}; mv_mult2s_bool(2, ms, v2, o); assert(o[0]==1 && o[1]==0);
    int v3[] = {0,1}; mv_mult2s_bool(2, ms, v3, o); assert(o[0]==1 && o[1]==0);
    int v4[] = {0,0}; mv_mult2s_bool(2, ms, v4, o); assert(o[0]==0 && o[1]==0);
    int v5[] = {1,1}; mv_mult2s_bool(2, ms, v5, o); assert(o[0]==1 && o[1]==0); // Repeat check
    int v6[] = {0,0}; mv_mult2s_bool(2, ms, v6, o); assert(o[0]==0 && o[1]==0); // Repeat check
    int v7[] = {1,0}; mv_mult2s_bool(2, ms, v7, o); assert(o[0]==1 && o[1]==0); // Repeat check

    // --- 2 Invalid Cases ---
    // 8. Wrong Matrix: int m_bad[]={0,0,0,0}; mv_mult2s_bool(2, m_bad, v1, o);
    // 9. Wrong n: mv_mult2s_bool(1, ms, v1, o);
}
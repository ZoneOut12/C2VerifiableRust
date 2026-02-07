// ========== Original Code (with ACSL) ==========
#include <stdio.h>

struct vector {
  int n;
  int* v;
};

/*@ ensures \result==0 || \result==1;
    assigns \nothing;
 */
int predicate(int v) {
  return v % 2 == 0;
}

/*@ requires \valid(a);
    requires \valid(o);
    requires \valid(a->v+(0..a->n-1));
    requires \valid(o->v+(0..a->n-1));
    requires \forall int i; \forall int j; 0 <= i < a->n && 0 <= j < a->n ==> \separated(a, o, a->v+i, o->v+j);
    requires a->n > 0;
    ensures 0 <= o->n <= a->n;
    ensures \forall int i; 0 <= i < o->n ==> 0 <= o->v[i] < a->n;
    ensures \forall int i; 0 < i < o->n ==> o->v[i-1] < o->v[i];
    assigns o->n, o->v[0..a->n-1];
 */
void index_where(struct vector* a, struct vector* o) {
  int n = a->n;
  o->n = 0;
  /*@
    loop invariant n == a->n;
    loop invariant 0 <= i <= n;
    loop invariant 0 <= o->n <= i;
    loop invariant \forall int j; 0 <= j < o->n ==> 0 <= o->v[j] < i;
    loop invariant \forall int j; 0 < j < o->n ==> o->v[j-1] < o->v[j];
    loop assigns i, o->n, o->v[0..n-1];
    loop variant n-i;
   */
  for (int i = 0; i < n; i++) {
    if (predicate(a->v[i])) {
      o->v[o->n++] = i;
    }
  }
}

// ========== Test Cases ==========
#include <assert.h>
#include <limits.h>
#include <stdlib.h>

void test_harness_predicate() {
    // Valid 1: Standard even
    assert(predicate(10) == 1);

    // Valid 2: Standard odd
    assert(predicate(11) == 0);

    // Valid 3: Zero
    assert(predicate(0) == 1);

    // Valid 4: Negative even
    assert(predicate(-20) == 1);

    // Valid 5: Negative odd
    // Note: -21 % 2 is -1 in C99, so (-1 == 0) is false (0)
    assert(predicate(-21) == 0);

    // Valid 6: Boundary Max
    assert(predicate(INT_MAX) == 0);

    // Valid 7: Boundary Min
    assert(predicate(INT_MIN) == 1);
}


// Assuming the struct vector and index_where are defined as provided

void test_case_1() {
    // Valid: All elements match (all even)
    int av[] = {2, 4, 6};
    int ov[3];
    struct vector a = {3, av};
    struct vector o = {0, ov}; // o.n starts at 0
    index_where(&a, &o);
    printf("test_case_1: o.n=%d, indices=[%d, %d, %d]\n", o.n, o.v[0], o.v[1], o.v[2]);
    // Expected: o.n=3, indices=[0, 1, 2]
}

void test_case_2() {
    // Valid: Mixed elements
    int av[] = {1, 2, 3};
    int ov[3];
    struct vector a = {3, av};
    struct vector o = {0, ov};
    index_where(&a, &o);
    printf("test_case_2: o.n=%d, indices=[%d]\n", o.n, o.v[0]);
    // Expected: o.n=1, indices=[1]
}

void test_case_3() {
    // Valid: No matches (all odd)
    int av[] = {1, 3, 5};
    int ov[3];
    struct vector a = {3, av};
    struct vector o = {0, ov};
    index_where(&a, &o);
    printf("test_case_3: o.n=%d\n", o.n);
    // Expected: o.n=0
}

void test_case_4() {
    // Valid: Alternating pattern including zero
    int av[] = {0, 1, 2, 3, 4};
    int ov[5];
    struct vector a = {5, av};
    struct vector o = {0, ov};
    index_where(&a, &o);
    printf("test_case_4: o.n=%d, indices=[%d, %d, %d]\n", o.n, o.v[0], o.v[1], o.v[2]);
    // Expected: o.n=3, indices=[0, 2, 4]
}

void test_case_5() {
    // Valid: Single element match
    int av[] = {8};
    int ov[1];
    struct vector a = {1, av};
    struct vector o = {0, ov};
    index_where(&a, &o);
    printf("test_case_5: o.n=%d, index=[%d]\n", o.n, o.v[0]);
    // Expected: o.n=1, index=[0]
}

void test_case_6() {
    // Invalid: a->v is NULL
    // Violates: requires \valid(a->v + (0..a->n-1))
    struct vector a = {3, NULL};
    int ov[3];
    struct vector o = {0, ov};
    // index_where(&a, &o); // Potential segmentation fault
}

void test_case_7() {
    // Invalid: a->n is 0
    // Violates: requires a->n > 0
    int av[] = {10, 20};
    struct vector a = {0, av};
    int ov[2];
    struct vector o = {0, ov};
    // index_where(&a, &o); // Violates precondition
}

void test_case_8() {
    // Boundary: Minimum size with match (zero)
    int av[] = {0};
    int ov[1];
    struct vector a = {1, av};
    struct vector o = {0, ov};
    index_where(&a, &o);
    printf("test_case_8: o.n=%d, index=[%d]\n", o.n, o.v[0]);
    // Expected: o.n=1, index=[0]
}

void test_case_9() {
    // Boundary: Minimum size no match
    int av[] = {7};
    int ov[1];
    struct vector a = {1, av};
    struct vector o = {0, ov};
    index_where(&a, &o);
    printf("test_case_9: o.n=%d\n", o.n);
    // Expected: o.n=0
}
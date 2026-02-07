// ========== Original Code (with ACSL) ==========
/*@ ensures \result==0 || \result==1;
    assigns \nothing;
 */
int predicate(int v) {
  return v % 2 == 0;
}

/*@ requires n > 0;
    requires \valid(v+(0..n-1));
    requires \valid(o+(0..n-1));
    ensures 0 <= \result <= n;
    ensures \forall int i; 0 <= i < \result ==> 0 <= o[i] < n;
    ensures \forall int i; 0 < i < \result ==> o[i-1] < o[i];
    assigns o[0..n-1];
 */
int index_where(int* v, int n, int* o) {
  int r = 0;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant 0 <= r <= i;
    loop invariant \forall int j; 0 <= j < r ==> 0 <= o[j] < i;
    loop invariant \forall int j; 0 < j < r ==> o[j-1] < o[j];
    loop assigns i, r, o[0..n-1];
    loop variant n-i;
   */
  for (int i = 0; i < n; i++) {
    if (predicate(v[i])) {
      o[r++] = i;
    }
  }
  return r;
}

// ========== Test Cases ==========
#include <assert.h>
#include <limits.h>

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


// Test case 1: Valid - normal case
void test_case_1() {
    int v[] = {1, 2, 3, 4, 5};
    int n = 5;
    int o[5];
    int result = index_where(v, n, o);
    printf("test_case_1: %d\n", result);  // Expected: 2
}

// Test case 2: Valid - all even
void test_case_2() {
    int v[] = {2, 4, 6};
    int n = 3;
    int o[3];
    int result = index_where(v, n, o);
    printf("test_case_2: %d\n", result);  // Expected: 3
}

// Test case 3: Valid - none even
void test_case_3() {
    int v[] = {1, 3, 5};
    int n = 3;
    int o[3];
    int result = index_where(v, n, o);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - even at first and third positions
void test_case_4() {
    int v[] = {2, 3, 4};
    int n = 3;
    int o[3];
    int result = index_where(v, n, o);
    printf("test_case_4: %d\n", result);  // Expected: 2
}

// Test case 5: Valid - single even element
void test_case_5() {
    int v[] = {2};
    int n = 1;
    int o[1];
    int result = index_where(v, n, o);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Boundary - single odd element
void test_case_6() {
    int v[] = {3};
    int n = 1;
    int o[1];
    int result = index_where(v, n, o);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - output array filled completely
void test_case_7() {
    int v[] = {2, 4};
    int n = 2;
    int o[2];
    int result = index_where(v, n, o);
    printf("test_case_7: %d\n", result);  // Expected: 2
}

// Test case 8: Invalid - n=0
void test_case_8() {
    int v[] = {1, 2, 3};
    int o[3];
    int result = index_where(v, 0, o); // n=0 invalid
}

// Test case 9: Invalid - v is NULL
void test_case_9() {
    int o[2];
    int result = index_where(NULL, 2, o); // v invalid
}

// Harness entry point
void test_harness_index_where() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
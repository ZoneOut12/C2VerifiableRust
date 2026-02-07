// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@\n  requires a < b  ==> b - a <= INT_MAX ;\n  requires b <= a ==> a - b <= INT_MAX ;\n\n  assigns \nothing ;\n\n  behavior inf:\n    assumes a < b ;\n    ensures a + \result == b ;\n\n  behavior sup:\n    assumes b <= a ;\n    ensures a - \result == b ;\n\n  complete behaviors ;\n  disjoint behaviors ;\n*/
int distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - normal case
void test_case_1() {
    int result = distance(5, 10);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - equal values
void test_case_2() {
    int result = distance(0, 0);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - negative and positive
void test_case_3() {
    int result = distance(-5, 3);
    printf("test_case_3: %d\n", result);  // Expected: 8
}

// Test case 4: Boundary - maximum positive difference
void test_case_4() {
    int result = distance(INT_MAX-1, INT_MAX);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - near minimum int
void test_case_5() {
    int result = distance(INT_MIN+1, INT_MIN+2);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Invalid - overflow in a < b case
void test_case_6() {
    int result = distance(INT_MIN, INT_MAX);  // Frama-C should flag this
}

// Test case 7: Invalid - overflow in b <= a case
void test_case_7() {
    int result = distance(INT_MAX, INT_MIN);  // Frama-C should flag this
}

// Test case 8: Boundary - maximum allowed difference
void test_case_8() {
    int result = distance(0, INT_MAX);
    printf("test_case_8: %d\n", result);  // Expected: INT_MAX
}

// Test case 9: Boundary - minimum values
void test_case_9() {
    int result = distance(INT_MIN, INT_MIN);
    printf("test_case_9: %d\n", result);  // Expected: 0
}

// Harness entry point (not main!)
void test_harness_distance() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid tests intentionally not called for output verification
}
void test_case_6() {
    int a = INT_MIN;
    int b = INT_MAX;
    int result = distance(a, b);
    assert(result == 4294967295);
}
void test_case_7() {
    int a = INT_MAX;
    int b = -1;
    int result = distance(a, b);
    assert(result == 2147483648);
}
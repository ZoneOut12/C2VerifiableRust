// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ requires ((((((((0<x0) && (x0<100)) && (0<x1)) && (x1<100)) && (0<=x2)) && (0<=x3)) && (x2<x0)) && (x3<x1)); assigns \nothing; ensures ((0<=\result) && (\result<(x0*x1)));
*/
int index_(int x0, int x1, int x2, int x3) {
  int x5 = x2 * x1;
  int x6 = x5 + x3;
  return x6;
}
/*@ predicate inv_matrix_Boolean(int* x26, integer x27, integer x28) = (((((x27<100) && (x28<100)) && (0<x27)) && (0<x28)) && (((x27*x28)>0) && \valid(x26+(0..(x27*x28)-1))));*/
/*@ requires (((inv_matrix_Boolean(x63,x64,x65) && inv_matrix_Boolean(x66,x67,x68)) && inv_matrix_Boolean(x69,x70,x71)) && ((((x64==x67) && (x64==x70)) && (x65==x68)) && (x65==x71)));
ensures ((inv_matrix_Boolean(x63,x64,x65) && inv_matrix_Boolean(x66,x67,x68)) && inv_matrix_Boolean(x69,x70,x71));
*/
void add(int *x63, int x64, int x65, int *x66, int x67, int x68, int *x69, int x70, int x71) {
  /*@ loop invariant 0<=x76<=x70; loop assigns x76, x69[(0..(x70*x71)-1)]; loop variant x70-x76; */
  for(int x76=0; x76 < x70; x76++) {
    /*@ loop invariant 0<=x78<=x71; loop assigns x78, x69[(0..(x70*x71)-1)]; loop variant x71-x78; */
    for(int x78=0; x78 < x71; x78++) {
      int x79 = index_(x64,x65,x76,x78);
      int x80 = x63[x79];
      int x81 = index_(x67,x68,x76,x78);
      int x82 = x66[x81];
      int x83 = x80 || x82;
      int x84 = index_(x70,x71,x76,x78);
      x69[x84] = x83;
    }
  }
}
/*@ requires ((inv_matrix_Boolean(x111,x112,x113) && inv_matrix_Boolean(x114,x115,x116)) && ((x112==x115) && (x113==x116)));
ensures (inv_matrix_Boolean(x111,x112,x113) && inv_matrix_Boolean(x114,x115,x116));
*/
void scalar_mult(int x110, int *x111, int x112, int x113, int *x114, int x115, int x116) {
  /*@ loop invariant 0<=x121<=x115; loop assigns x121, x114[(0..(x115*x116)-1)]; loop variant x115-x121; */
  for(int x121=0; x121 < x115; x121++) {
    /*@ loop invariant 0<=x123<=x116; loop assigns x123, x114[(0..(x115*x116)-1)]; loop variant x116-x123; */
    for(int x123=0; x123 < x116; x123++) {
      int x126;
      if (x110) {
        int x124 = index_(x112,x113,x121,x123);
        int x125 = x111[x124];
        x126 = x125;
      } else {
        x126 = 0/*false*/;
      }
      int x127 = index_(x115,x116,x121,x123);
      x114[x127] = x126;
    }
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal values
void test_case_1() {
    int result = index_(50, 50, 25, 25);
    printf("test_case_1: %d\n", result);  // Expected: 1275
}

// Test case 2: Valid - minimum valid dimensions
void test_case_2() {
    int result = index_(2, 3, 1, 2);
    printf("test_case_2: %d\n", result);  // Expected: 5
}

// Test case 3: Valid - maximum dimensions with zero indices
void test_case_3() {
    int result = index_(99, 99, 0, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - edge indices
void test_case_4() {
    int result = index_(10, 20, 9, 19);
    printf("test_case_4: %d\n", result);  // Expected: 199
}

// Test case 5: Valid - square matrix maximum indices
void test_case_5() {
    int result = index_(5, 5, 4, 4);
    printf("test_case_5: %d\n", result);  // Expected: 24
}

// Test case 6: Invalid - x0 <= 0
void test_case_6() {
    int result = index_(0, 50, 0, 0);
    // Frama-C should flag this
}

// Test case 7: Invalid - x2 >= x0
void test_case_7() {
    int result = index_(5, 5, 5, 4);
    // Frama-C should flag this
}

// Test case 8: Boundary - minimum dimensions (1x1)
void test_case_8() {
    int result = index_(1, 1, 0, 0);
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary - maximum dimensions with max indices
void test_case_9() {
    int result = index_(99, 99, 98, 98);
    printf("test_case_9: %d\n", result);  // Expected: 9800
}

// Harness entry point (not main!)
void test_harness_index_() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid cases intentionally not called - for precondition testing
}

void print_matrix_simple(const char* name, int* C, int rows, int cols) {
    printf("%s: ", name);
    for (int i = 0; i < rows * cols; i++) {
        printf("%d ", C[i]);
    }
    printf("\n");
}

// --- add() Test Cases ---

// Test case 10: Valid - Basic Addition (1x2)
void test_case_10() {
    int A[] = {1, 0};
    int B[] = {0, 1};
    int C[2] = {0};
    add(A, 1, 2, B, 1, 2, C, 1, 2);
    print_matrix_simple("test_case_10", C, 1, 2); // Expected: 1 1
}

// Test case 11: Valid - All Zeroes
void test_case_11() {
    int A[] = {0, 0, 0, 0};
    int B[] = {0, 0, 0, 0};
    int C[4] = {1, 1, 1, 1}; // Start with 1s
    add(A, 2, 2, B, 2, 2, C, 2, 2);
    print_matrix_simple("test_case_11", C, 2, 2); // Expected: 0 0 0 0
}

// Test case 12: Valid - Identity logic
void test_case_12() {
    int A[] = {1, 1, 1, 1};
    int B[] = {0, 0, 0, 0};
    int C[4] = {0};
    add(A, 2, 2, B, 2, 2, C, 2, 2);
    print_matrix_simple("test_case_12", C, 2, 2); // Expected: 1 1 1 1
}

// --- scalar_mult() Test Cases ---

// Test case 13: Valid - Scalar 1 (Identity)
void test_case_13() {
    int A[] = {1, 0, 1, 0};
    int C[4] = {0};
    scalar_mult(1, A, 2, 2, C, 2, 2);
    print_matrix_simple("test_case_13", C, 2, 2); // Expected: 1 0 1 0
}

// Test case 14: Valid - Scalar 0 (Nullify)
void test_case_14() {
    int A[] = {1, 1, 1, 1};
    int C[4] = {1, 1, 1, 1};
    scalar_mult(0, A, 2, 2, C, 2, 2);
    print_matrix_simple("test_case_14", C, 2, 2); // Expected: 0 0 0 0
}

// Test case 15: Valid - 1x1 Boundary
void test_case_15() {
    int A[] = {1};
    int C[1] = {0};
    scalar_mult(1, A, 1, 1, C, 1, 1);
    print_matrix_simple("test_case_15", C, 1, 1); // Expected: 1
}

// Test case 16: Valid - Larger Rectangular (3x2)
void test_case_16() {
    int A[] = {1, 0, 1, 1, 0, 0};
    int B[] = {0, 0, 1, 0, 1, 1};
    int C[6] = {0};
    add(A, 3, 2, B, 3, 2, C, 3, 2);
    print_matrix_simple("test_case_16", C, 3, 2); // Expected: 1 0 1 1 1 1
}

// --- Invalid Cases ---

// Test case 17: Invalid - Dimension Mismatch (add)
void test_case_17() {
    int A[4], B[6], C[4];
    add(A, 2, 2, B, 3, 2, C, 2, 2); // Violation: x64 != x67
}

// Test case 18: Invalid - Dimension >= 100
void test_case_18() {
    int A[100], C[100];
    scalar_mult(1, A, 105, 1, C, 105, 1); // Violation: x112 < 100
}
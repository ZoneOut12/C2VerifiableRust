// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires ((((((((0<x0) &&
(x0<100)) &&
(0<x1)) &&
(x1<100)) &&
(0<=x2)) &&
(0<=x3)) &&
(x2<x0)) &&
(x3<x1));
assigns \nothing;
ensures ((0<=\result) &&
(\result<(x0*x1)));
*/
int index_(int  x0, int  x1, int  x2, int  x3) {
  int x5 = x2 * x1;
  int x6 = x5 + x3;
  return x6;
}
/*@ predicate inv_matrix_Boolean(int* x26, integer  x27, integer  x28) = (((((x27<100) &&
(x28<100)) &&
(0<x27)) &&
(0<x28)) &&
(((x27*x28)>0) &&
\valid(x26+(0..(x27*x28)-1))));*/
/*@
requires (((inv_matrix_Boolean(x63,x64,x65) &&
inv_matrix_Boolean(x66,x67,x68)) &&
inv_matrix_Boolean(x69,x70,x71)) &&
(((x65==x67) &&
(x64==x70)) &&
(x68==x71)));
ensures ((inv_matrix_Boolean(x63,x64,x65) &&
inv_matrix_Boolean(x66,x67,x68)) &&
inv_matrix_Boolean(x69,x70,x71));
*/
void mult(int  * x63, int  x64, int  x65, int  * x66, int  x67, int  x68, int  * x69, int  x70, int  x71) {
  /*@
  loop invariant 0<=x76<=x64;
  loop assigns x76, x69[(0..(x70*x71)-1)];
  loop variant x64-x76;
  */
  for(int x76=0; x76 < x64; x76++) {
    /*@
    loop invariant 0<=x78<=x68;
    loop assigns x78, x69[(0..(x70*x71)-1)];
    loop variant x68-x78;
    */
    for(int x78=0; x78 < x68; x78++) {
      int x79 = index_(x70,x71,x76,x78);
      x69[x79] = 0/*false*/;
      /*@
      loop invariant 0<=x82<=x65;
      loop assigns x82, x69[(0..(x70*x71)-1)];
      loop variant x65-x82;
      */
      for(int x82=0; x82 < x65; x82++) {
        int x83 = x69[x79];
        int x84 = index_(x64,x65,x76,x82);
        int x85 = x63[x84];
        int x88;
        if (x85) {
          int x86 = index_(x67,x68,x82,x78);
          int x87 = x66[x86];
          x88 = x87;
        } else {
          x88 = 0/*false*/;
        }
        int x89 = x83 || x88;
        x69[x79] = x89;
      }
    }
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - typical values
void test_case_1() {
    int result = index_(5, 5, 2, 3);
    printf("test_case_1: %d\n", result);  // Expected: 13
}

// Test case 2: Valid - minimum x2 and x3
void test_case_2() {
    int result = index_(10, 20, 0, 0);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - mid-range values
void test_case_3() {
    int result = index_(2, 3, 1, 2);
    printf("test_case_3: %d\n", result);  // Expected: 5
}

// Test case 4: Boundary - minimum dimensions
void test_case_4() {
    int result = index_(1, 1, 0, 0);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Boundary - maximum dimensions
void test_case_5() {
    int result = index_(99, 99, 98, 98);
    printf("test_case_5: %d\n", result);  // Expected: 9800
}

// Test case 6: Invalid - x0 <= 0
void test_case_6() {
    int result = index_(0, 5, 0, 3);  // Frama-C should flag this
    // No output check needed for invalid case
}

// Test case 7: Invalid - x3 >= x1
void test_case_7() {
    int result = index_(5, 5, 2, 5);  // Frama-C should flag this
    // No output check needed for invalid case
}

// Test case 8: Valid - another valid case
void test_case_8() {
    int result = index_(3, 4, 2, 3);
    printf("test_case_8: %d\n", result);  // Expected: 11
}

// Test case 9: Valid - mid-range values
void test_case_9() {
    int result = index_(50, 50, 25, 25);
    printf("test_case_9: %d\n", result);  // Expected: 1275
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
    // Invalid test cases intentionally not called - for precondition testing
}

void print_matrix_result(const char* name, int* C, int rows, int cols) {
    printf("%s: ", name);
    for (int i = 0; i < rows * cols; i++) {
        printf("%d ", C[i]);
    }
    printf("\n");
}

// Test case 10: Valid - Identity * Matrix
void test_case_10() {
    int A[] = {1, 0, 0, 1}; // 2x2 Identity
    int B[] = {1, 1, 0, 1}; // 2x2
    int C[4] = {0};
    mult(A, 2, 2, B, 2, 2, C, 2, 2);
    print_matrix_result("test_case_10", C, 2, 2); // Expected: 1 1 0 1
}

// Test case 11: Valid - Zero * Matrix
void test_case_11() {
    int A[] = {0, 0, 0, 0};
    int B[] = {1, 1, 1, 1};
    int C[4] = {1, 1, 1, 1}; 
    mult(A, 2, 2, B, 2, 2, C, 2, 2);
    print_matrix_result("test_case_11", C, 2, 2); // Expected: 0 0 0 0
}

// Test case 12: Valid - Rectangular (2x3 * 3x2)
void test_case_12() {
    int A[] = {1, 0, 1, 0, 1, 0}; // 2x3
    int B[] = {1, 0, 1, 1, 0, 1}; // 3x2
    int C[4] = {0};
    mult(A, 2, 3, B, 3, 2, C, 2, 2);
    print_matrix_result("test_case_12", C, 2, 2); // Expected: 1 1 1 1
}

// Test case 13: Valid - Single element matrices (1x1)
void test_case_13() {
    int A[] = {1}; int B[] = {1}; int C[1] = {0};
    mult(A, 1, 1, B, 1, 1, C, 1, 1);
    print_matrix_result("test_case_13", C, 1, 1); // Expected: 1
}

// Test case 14: Valid - All ones result
void test_case_14() {
    int A[] = {1, 1}; // 1x2
    int B[] = {1, 1}; // 2x1 (Transposed)
    int C[1] = {0};
    mult(A, 1, 2, B, 2, 1, C, 1, 1);
    print_matrix_result("test_case_14", C, 1, 1); // Expected: 1
}

// Test case 15: Valid - 3x1 * 1x3 (Large outer dimensions)
void test_case_15() {
    int A[] = {1, 0, 1}; // 3x1
    int B[] = {1, 1, 1}; // 1x3
    int C[9] = {0};
    mult(A, 3, 1, B, 1, 3, C, 3, 3);
    print_matrix_result("test_case_15", C, 3, 3); // Expected: 1 1 1 0 0 0 1 1 1
}

// Test case 16: Valid - Sparse Boolean multiplication
void test_case_16() {
    int A[] = {1, 0, 0, 0}; // 2x2
    int B[] = {0, 0, 0, 1}; // 2x2
    int C[4] = {1, 1, 1, 1};
    mult(A, 2, 2, B, 2, 2, C, 2, 2);
    print_matrix_result("test_case_16", C, 2, 2); // Expected: 0 0 0 0
}

// Test case 17: Invalid - Dimension Mismatch (ACSL requires x65 == x67)
void test_case_17() {
    int A[4], B[4], C[4];
    mult(A, 2, 2, B, 3, 2, C, 2, 2); // Frama-C flags x65(2) != x67(3)
}

// Test case 18: Invalid - Dimension too large (ACSL x27 < 100)
void test_case_18() {
    int A[100], B[100], C[100];
    mult(A, 150, 2, B, 2, 2, C, 150, 2); // Frama-C flags x64 < 100 violation
}
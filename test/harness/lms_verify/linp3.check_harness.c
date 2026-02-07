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
requires (((((inv_matrix_Boolean(x63,x64,x65) &&
inv_matrix_Boolean(x66,x67,x68)) &&
inv_matrix_Boolean(x69,x70,x71)) &&
((x70==x64) &&
(x71==x65))) &&
((x70==x67) &&
(x71==x68))) &&
((\forall int  x121; (\forall int  x122; ((((0<=x121) &&
(x121<(x70*x71))) &&
((0<=x122) &&
(x122<(x64*x65)))) ==> \separated(x69+x121,x63+x122)))) &&
(\forall int  x136; (\forall int  x137; ((((0<=x136) &&
(x136<(x70*x71))) &&
((0<=x137) &&
(x137<(x67*x68)))) ==> \separated(x69+x136,x66+x137))))));
ensures (((inv_matrix_Boolean(x63,x64,x65) &&
inv_matrix_Boolean(x66,x67,x68)) &&
inv_matrix_Boolean(x69,x70,x71)) &&
(\forall int  x157; (((0<=x157) &&
(x157<(x70*x71))) ==> (x69[x157]==(x63[x157] || x66[x157])))));
*/
void add(int  * x63, int  x64, int  x65, int  * x66, int  x67, int  x68, int  * x69, int  x70, int  x71) {
  /*@assert \separated(x69+0,x63+0);*/
  /*@assert \separated(x69+0,x66+0);*/
  int x73 = x70 * x71;
  /*@
  loop invariant 0<=x81<=x73;
  loop invariant (\forall int  x82; (((0<=x82) &&
  (x82<x81)) ==> (x69[x82]==(x63[x82] || x66[x82]))));
  loop assigns x81, x69[(0..x73-1)];
  loop variant x73-x81;
  */
  for(int x81=0; x81 < x73; x81++) {
    int x94 = x63[x81];
    int x95 = x66[x81];
    int x96 = x94 || x95;
    x69[x81] = x96;
    /*@assert \separated(x69+x81,x63+x81);*/
    /*@assert \separated(x69+x81,x66+x81);*/
  }
}
/*@
requires (((inv_matrix_Boolean(x172,x173,x174) &&
inv_matrix_Boolean(x175,x176,x177)) &&
((x176==x173) &&
(x177==x174))) &&
(\forall int  x213; (\forall int  x214; ((((0<=x213) &&
(x213<(x176*x177))) &&
((0<=x214) &&
(x214<(x173*x174)))) ==> \separated(x175+x213,x172+x214)))));
requires \forall int i; 0 <= i < x173 * x174 ==> x172[i] == 0 || x172[i] == 1;
ensures (((inv_matrix_Boolean(x172,x173,x174) &&
inv_matrix_Boolean(x175,x176,x177)) &&
(\forall int  x233; (((0<=x233) &&
(x233<(x176*x177))) ==> (x175[x233]==(x171 &&
x172[x233]))))) &&
((x171==\false) ==> (\forall int x247; (0<=x247<x176) ==> (\forall int x250; (0<=x250<x177) ==> (x175[((x247*x177)+x250)]==\false)))));
*/
void scalar_mult(int  x171, int  * x172, int  x173, int  x174, int  * x175, int  x176, int  x177) {
  /*@assert \separated(x175+0,x172+0);*/
  int x179 = x176 * x177;
  /*@
  loop invariant 0<=x184<=x179;
  loop invariant (\forall int  x185; (((0<=x185) &&
  (x185<x184)) ==> (x175[x185]==(x171 &&
  x172[x185]))));
  loop assigns x184, x175[(0..x179-1)];
  loop variant x179-x184;
  */
  for(int x184=0; x184 < x179; x184++) {
    int x197;
    if (x171) {
      int x196 = x172[x184];
      x197 = x196;
    } else {
      x197 = 0/*false*/;
    }
    x175[x184] = x197;
    /*@assert \separated(x175+x184,x172+x184);*/
  }
}


// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal case
void test_case_1() {
    int result = index_(5, 10, 3, 5);
    printf("test_case_1: %d\n", result);  // Expected: 35
}

// Test case 2: Valid - maximum dimensions
void test_case_2() {
    int result = index_(99, 99, 98, 98);
    printf("test_case_2: %d\n", result);  // Expected: 9800
}

// Test case 3: Valid - minimal dimensions with edge values
void test_case_3() {
    int result = index_(2, 2, 0, 1);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - mid-range values
void test_case_4() {
    int result = index_(10, 20, 5, 15);
    printf("test_case_4: %d\n", result);  // Expected: 115
}

// Test case 5: Valid - minimal dimensions
void test_case_5() {
    int result = index_(1, 1, 0, 0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - x0=0
void test_case_6() {
    int result = index_(0, 5, 0, 0);  // Frama-C should flag this
}

// Test case 7: Invalid - x2 >= x0 and x3 >= x1
void test_case_7() {
    int result = index_(5, 5, 5, 5);  // Frama-C should flag this
}

// Test case 8: Boundary - minimal dimensions
void test_case_8() {
    int result = index_(1, 1, 0, 0);
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary - maximum allowed values
void test_case_9() {
    int result = index_(99, 99, 98, 98);
    printf("test_case_9: %d\n", result);  // Expected: 9800
}

// Harness entry point
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

// Helper to print matrix results
void print_result(const char* name, int* res, int r, int c) {
    printf("%s: ", name);
    for(int i = 0; i < r * c; i++) printf("%d ", res[i]);
    printf("\n");
}

// ========== add() Test Cases (Total 9) ==========

void test_add_valid() {
    // 1. Normal 2x2 addition (OR logic)
    int A1[] = {1, 0, 0, 1}, B1[] = {0, 1, 0, 1}, C1[4];
    add(A1, 2, 2, B1, 2, 2, C1, 2, 2);
    print_result("add_1", C1, 2, 2); // Expected: 1 1 0 1

    // 2. All zeros
    int A2[] = {0, 0}, B2[] = {0, 0}, C2[2];
    add(A2, 1, 2, B2, 1, 2, C2, 1, 2);
    print_result("add_2", C2, 1, 2); // Expected: 0 0

    // 3. All ones (1 || 1 = 1)
    int A3[] = {1, 1}, B3[] = {1, 1}, C3[2];
    add(A3, 1, 2, B3, 1, 2, C3, 1, 2);
    print_result("add_3", C3, 1, 2); // Expected: 1 1

    // 4. 1x1 Boundary
    int A4[] = {0}, B4[] = {1}, C4[1];
    add(A4, 1, 1, B4, 1, 1, C4, 1, 1);
    print_result("add_4", C4, 1, 1); // Expected: 1

    // 5. Rectangular 3x2
    int A5[] = {1,0, 0,1, 1,1}, B5[] = {0,0, 1,1, 0,0}, C5[6];
    add(A5, 3, 2, B5, 3, 2, C5, 3, 2);
    print_result("add_5", C5, 3, 2); // Expected: 1 0 1 1 1 1

    // 6. Max dimensions (99x1)
    int A6[99] = {0}, B6[99] = {0}, C6[99];
    A6[98] = 1; 
    add(A6, 99, 1, B6, 99, 1, C6, 99, 1);
    printf("add_6: C[98]=%d\n", C6[98]); // Expected: 1

    // 7. Identity-like (A + Zero = A)
    int A7[] = {1, 0, 1}, B7[] = {0, 0, 0}, C7[3];
    add(A7, 1, 3, B7, 1, 3, C7, 1, 3);
    print_result("add_7", C7, 1, 3); // Expected: 1 0 1
}

void test_add_invalid() {
    int A[4], B[4], C[4];
    // 8. Invalid: Dimension mismatch (x64 != x67)
    // add(A, 2, 2, B, 1, 4, C, 2, 2); 
    // 9. Invalid: Out of ACSL range (x64 >= 100)
    // add(A, 105, 1, B, 105, 1, C, 105, 1);
}

// ========== scalar_mult() Test Cases (Total 9) ==========

void test_scalar_valid() {
    // 1. Scalar 1 (Identity)
    int A1[] = {1, 0, 1, 1}, C1[4];
    scalar_mult(1, A1, 2, 2, C1, 2, 2);
    print_result("scalar_1", C1, 2, 2); // Expected: 1 0 1 1

    // 2. Scalar 0 (Nullify)
    int A2[] = {1, 1, 1, 1}, C2[4];
    scalar_mult(0, A2, 2, 2, C2, 2, 2);
    print_result("scalar_2", C2, 2, 2); // Expected: 0 0 0 0

    // 3. 1x1 Boundary
    int A3[] = {1}, C3[1];
    scalar_mult(1, A3, 1, 1, C3, 1, 1);
    print_result("scalar_3", C3, 1, 1); // Expected: 1

    // 4. All zeros input
    int A4[] = {0, 0, 0}, C4[3];
    scalar_mult(1, A4, 1, 3, C4, 1, 3);
    print_result("scalar_4", C4, 1, 3); // Expected: 0 0 0

    // 5. Rectangular 2x3
    int A5[] = {1,1,1, 0,0,0}, C5[6];
    scalar_mult(1, A5, 2, 3, C5, 2, 3);
    print_result("scalar_5", C5, 2, 3); // Expected: 1 1 1 0 0 0

    // 6. Max dimensions (1x99)
    int A6[99], C6[99]; A6[0] = 1;
    scalar_mult(1, A6, 1, 99, C6, 1, 99);
    printf("scalar_6: C[0]=%d\n", C6[0]); // Expected: 1

    // 7. Scalar 1 on sparse matrix
    int A7[] = {0, 0, 1, 0}, C7[4];
    scalar_mult(1, A7, 2, 2, C7, 2, 2);
    print_result("scalar_7", C7, 2, 2); // Expected: 0 0 1 0
}

void test_scalar_invalid() {
    int A[4], C[4];
    // 8. Invalid: Pointer is NULL (inv_matrix_Boolean violation)
    // scalar_mult(1, NULL, 2, 2, C, 2, 2);
    // 9. Invalid: x112 <= 0 violation
    // scalar_mult(1, A, 0, 2, C, 0, 2);
}
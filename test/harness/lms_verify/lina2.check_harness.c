// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires (((x1>0) &&
\valid(x0+(0..x1-1))) &&
\valid(x2+(0..x1-1)));
ensures ((((0<=\result) &&
(\result<=x1)) &&
(\forall int  x74; (((0<=x74) &&
(x74<\result)) ==> ((0<=x2[x74]) &&
(x2[x74]<x1))))) &&
(\forall int  x86; (((0<x86) &&
(x86<\result)) ==> (x2[(x86-1)]<x2[x86]))));
assigns x2[(0..x1-1)];
*/
int index_where_even(int  * x0, int  x1, int  * x2) {
  int x5 = 0;
  /*@
  loop invariant ((((((0<=x6) &&
  (x6<=x1)) &&
  (0<=x5)) &&
  (x5<=x6)) &&
  (\forall int  x28; (((0<=x28) &&
  (x28<x5)) ==> ((0<=x2[x28]) &&
  (x2[x28]<x6))))) &&
  (\forall int  x42; (((0<x42) &&
  (x42<x5)) ==> (x2[(x42-1)]<x2[x42]))));
  loop assigns x6, x5, x2[(0..x1-1)];
  loop variant (x1-x6);
  */
  for(int x6=0; x6 < x1; x6++) {
    int x7 = x0[x6];
    int x8 = x7 % 2;
    int x9 = x8 == 0;
    if (x9) {
      int x10 = x5;
      x2[x10] = x6;
      x5 += 1;
    } else {
    }
  }
  int x62 = x5;
  return x62;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal mixed even/odd
void test_case_1() {
    int x0[] = {1,2,3,4,5};
    int x2[5];
    int result = index_where_even(x0, 5, x2);
    printf("test_case_1: %d\n", result);  // Expected: 2
}

// Test case 2: Valid - all even
void test_case_2() {
    int x0[] = {2,4,6};
    int x2[3];
    int result = index_where_even(x0, 3, x2);
    printf("test_case_2: %d\n", result);  // Expected: 3
}

// Test case 3: Valid - no even elements
void test_case_3() {
    int x0[] = {1,3,5};
    int x2[3];
    int result = index_where_even(x0, 3, x2);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - zero and increasing
void test_case_4() {
    int x0[] = {0,1,2,3,4};
    int x2[5];
    int result = index_where_even(x0, 5, x2);
    printf("test_case_4: %d\n", result);  // Expected: 3
}

// Test case 5: Valid - single even
void test_case_5() {
    int x0[] = {0};
    int x2[1];
    int result = index_where_even(x0, 1, x2);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Invalid - x1 = 0
void test_case_6() {
    int x0[] = {1,2};
    int x2[2];
    int result = index_where_even(x0, 0, x2);  // Frama-C should flag this
}

// Test case 7: Invalid - x0 = NULL
void test_case_7() {
    int x2[2];
    int result = index_where_even(NULL, 2, x2);  // Frama-C should flag this
}

// Test case 8: Boundary - minimum valid x1
void test_case_8() {
    int x0[] = {0};
    int x2[1];
    int result = index_where_even(x0, 1, x2);
    printf("test_case_8: %d\n", result);  // Expected: 1
}

// Test case 9: Boundary - two even elements
void test_case_9() {
    int x0[] = {0,2};
    int x2[2];
    int result = index_where_even(x0, 2, x2);
    printf("test_case_9: %d\n", result);  // Expected: 2
}

// Harness entry point (not main!)
void test_harness_index_where_even() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}
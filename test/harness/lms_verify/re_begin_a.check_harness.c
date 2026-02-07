// ========== Original Code (with ACSL) ==========
/*@ requires ((strlen(x0)>=0) && 
\valid(x0+(0..strlen(x0))));
*/
int matcher(char  * x0) {
  int x2 = strlen(x0);
  int x3 = 0 < x2;
  int x6;
  if (x3) {
    char x4 = x0[0];
    int x5 = 'a' == x4;
    x6 = x5;
  } else {
    x6 = 0/*false*/;
  }
  int x7;
  if (x6) {
    x7 = 1/*true*/;
  } else {
    x7 = 0/*false*/;
  }
  return x7;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid string starting with 'a'
void test_case_1() {
    char *x0 = "apple";
    int result = matcher(x0);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid string not starting with 'a'
void test_case_2() {
    char *x0 = "banana";
    int result = matcher(x0);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid string with mixed characters
void test_case_3() {
    char *x0 = "test123";
    int result = matcher(x0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid string starting with 'a'
void test_case_4() {
    char *x0 = "another";
    int result = matcher(x0);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid string not starting with 'a'
void test_case_5() {
    char *x0 = "xyz";
    int result = matcher(x0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - empty string
void test_case_6() {
    char *x0 = "";
    int result = matcher(x0);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - single 'a' character
void test_case_7() {
    char *x0 = "a";
    int result = matcher(x0);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    char *x0 = NULL;
    int result = matcher(x0);
    // Frama-C should flag this
}

// Test case 9: Invalid - non-null-terminated array
void test_case_9() {
    char x0[2] = {'x', 'y'};
    int result = matcher(x0);
    // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_matcher() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <string.h>
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
*/
int matcher_begin_a(char  * x0) {
  char x2 = x0[0];
  int x3 = x2 == '\0';
  int x6;
  if (x3) {
    x6 = 0/*false*/;
  } else {
    int x5 = 'a' == x2;
    x6 = x5;
  }
  int x8;
  if (x6) {
    x8 = 1/*true*/;
  } else {
    x8 = 0/*false*/;
  }
  return x8;
}

// ========== Test Cases ==========
#include <stdio.h>

// Valid test cases
void test_case_1() {
    char str[] = "a";
    int result = matcher_begin_a(str);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

void test_case_2() {
    char str[] = "apple";
    int result = matcher_begin_a(str);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

void test_case_3() {
    char str[] = "b";
    int result = matcher_begin_a(str);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

void test_case_4() {
    char str[] = "xyz";
    int result = matcher_begin_a(str);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

void test_case_5() {
    char str[] = "hello";
    int result = matcher_begin_a(str);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Boundary test cases
void test_case_6() {
    char str[] = "";
    int result = matcher_begin_a(str);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

void test_case_7() {
    char str[] = "a";
    int result = matcher_begin_a(str);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Invalid test cases
void test_case_8() {
    int result = matcher_begin_a(NULL);  // Frama-C should flag this
}

void test_case_9() {
    char arr[2] = {'a', 'b'};
    int result = matcher_begin_a(arr);  // Frama-C should flag this
}

// Harness entry point
void test_harness_matcher_begin_a() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called
}
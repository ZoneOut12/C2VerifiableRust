// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <string.h>
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
assigns \nothing;
ensures ((\result==-1) || ((0<=\result) &&
(\result<=9)));
*/
int p(char  * x0) {
  int x8 = -1;
  int x9 = 1/*true*/;
  char x10 = '\0';
  char  *x11 = 0/*null*/;
  char x2 = x0[0];
  int x3 = x2 == '\0';
  if (x3) {
    x11 = x0;
  } else {
    int x4 = x2 >= '0';
    int x6;
    if (x4) {
      int x5 = x2 <= '9';
      x6 = x5;
    } else {
      x6 = 0/*false*/;
    }
    if (x6) {
      x9 = 0/*false*/;
      x10 = x2;
      char  *x7 = x0+1;
      x11 = x7;
    } else {
      x11 = x0;
    }
  }
  int x23 = x9;
  if (x23) {
    char  *x24 = x11;
  } else {
    char x26 = x10;
    char  *x28 = x11;
    char x27 = x26 - '0';
    x8 = x27;
  }
  int x32 = x8;
  return x32;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - empty string
void test_case_1() {
    char x0[] = "";
    int result = p(x0);
    printf("test_case_1: %d\n", result);  // Expected: -1
}

// Test case 2: Valid - single digit '5'
void test_case_2() {
    char x0[] = "5";
    int result = p(x0);
    printf("test_case_2: %d\n", result);  // Expected: 5
}

// Test case 3: Valid - non-digit first character
void test_case_3() {
    char x0[] = "a";
    int result = p(x0);
    printf("test_case_3: %d\n", result);  // Expected: -1
}

// Test case 4: Valid - digit followed by other characters
void test_case_4() {
    char x0[] = "3xyz";
    int result = p(x0);
    printf("test_case_4: %d\n", result);  // Expected: 3
}

// Test case 5: Valid - non-digit first character with more characters
void test_case_5() {
    char x0[] = "X123";
    int result = p(x0);
    printf("test_case_5: %d\n", result);  // Expected: -1
}

// Test case 6: Boundary - empty string
void test_case_6() {
    char x0[] = "";
    int result = p(x0);
    printf("test_case_6: %d\n", result);  // Expected: -1
}

// Test case 7: Boundary - maximum digit '9'
void test_case_7() {
    char x0[] = "9";
    int result = p(x0);
    printf("test_case_7: %d\n", result);  // Expected: 9
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    int result = p(NULL);  // Frama-C should flag this
}

// Test case 9: Invalid - non-null-terminated string
void test_case_9() {
    char arr[1] = {'a'};
    int result = p(arr);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_p() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called
}
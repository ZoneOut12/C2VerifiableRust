// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <string.h>
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
*/
int matcher_a(char  * x0) {
  int x2 = 0/*false*/;
  int x3 = 1/*true*/;
  char  *x4 = x0;
  /*@
  loop invariant ((strlen(x4)>=0) &&
  \valid(x4+(0..strlen(x4))));
  loop assigns x2, x3, x4;
  loop variant ((strlen(x4)+((x2) ? (0) : (1)))+((x3) ? (1) : (0)));
  */
  for (;;) {
    int x5 = x2;
    int x9;
    if (x5) {
      x9 = 0/*false*/;
    } else {
      int x7 = x3;
      x9 = x7;
    }
    if (!x9) break;
    char  *x11 = x4;
    char x12 = x11[0];
    int x13 = x12 == '\0';
    int x16;
    if (x13) {
      x16 = 0/*false*/;
    } else {
      int x15 = 'a' == x12;
      x16 = x15;
    }
    int x18;
    if (x16) {
      x18 = 1/*true*/;
    } else {
      x18 = 0/*false*/;
    }
    x2 = x18;
    int x20 = x2;
    if (x20) {
    } else {
      int x14 = !x13;
      x3 = x14;
      int x23 = x3;
      if (x23) {
        char  *x17 = x11+1;
        x4 = x17;
      } else {
      }
    }
  }
  int x54 = x2;
  return x54;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - string containing 'a'
void test_case_1() {
    char x0[] = "abc";
    int result = matcher_a(x0);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - string without 'a'
void test_case_2() {
    char x0[] = "bcd";
    int result = matcher_a(x0);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - 'a' at first position
void test_case_3() {
    char x0[] = "apple";
    int result = matcher_a(x0);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - multiple 'a's
void test_case_4() {
    char x0[] = "zappa";
    int result = matcher_a(x0);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - no 'a's
void test_case_5() {
    char x0[] = "xyz";
    int result = matcher_a(x0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - empty string
void test_case_6() {
    char x0[] = "";
    int result = matcher_a(x0);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - single 'a'
void test_case_7() {
    char x0[] = "a";
    int result = matcher_a(x0);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    char *x0 = NULL;
    int result = matcher_a(x0);  // Frama-C should flag this
}

// Test case 9: Invalid - non-null-terminated buffer
void test_case_9() {
    char arr[5] = {'a', 'b', 'c', 'd', 'e'};
    int result = matcher_a(arr);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_matcher_a() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - for precondition testing
}
void test_case_8() {
    matcher_a(NULL);
}

void test_case_9() {
    char str[] = {'a', 'b'}; // No null terminator
    matcher_a(str);
}
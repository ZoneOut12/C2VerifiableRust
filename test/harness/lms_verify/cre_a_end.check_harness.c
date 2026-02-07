// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <string.h>
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
*/
int matcher_a_end(char  * x0) {
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
    int x20;
    if (x16) {
      char  *x17 = x11+1;
      char x18 = x17[0];
      int x19 = x18 == '\0';
      x20 = x19;
    } else {
      x20 = 0/*false*/;
    }
    x2 = x20;
    int x22 = x2;
    if (x22) {
    } else {
      int x14 = !x13;
      x3 = x14;
      int x25 = x3;
      if (x25) {
        char  *x17 = x11+1;
        x4 = x17;
      } else {
      }
    }
  }
  int x56 = x2;
  return x56;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - string ending with 'a'
void test_case_1() {
    char str[] = "ba";
    int result = matcher_a_end(str);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - string ending with 'a'
void test_case_2() {
    char str[] = "testa";
    int result = matcher_a_end(str);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - multiple 'a's
void test_case_3() {
    char str[] = "aaaa";
    int result = matcher_a_end(str);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - not ending with 'a'
void test_case_4() {
    char str[] = "abc";
    int result = matcher_a_end(str);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - not ending with 'a'
void test_case_5() {
    char str[] = "hello";
    int result = matcher_a_end(str);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - empty string
void test_case_6() {
    char str[] = "";
    int result = matcher_a_end(str);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - single 'a'
void test_case_7() {
    char str[] = "a";
    int result = matcher_a_end(str);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    matcher_a_end(NULL);  // Frama-C should flag this
}

// Test case 9: Invalid - non-null-terminated array
void test_case_9() {
    char arr[] = {'x'};  // Not null-terminated
    matcher_a_end(arr);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_matcher_a_end() {
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
    matcher_a_end(NULL);
}

void test_case_9() {
    char buffer[4] = {'a', 'b', 'c', 'd'};
    matcher_a_end(buffer);
}
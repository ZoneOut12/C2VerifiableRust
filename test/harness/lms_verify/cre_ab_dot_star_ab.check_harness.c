// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <string.h>
/*@
requires ((strlen(x0)>=0) &&
\valid(x0+(0..strlen(x0))));
*/
int matcher_ab_dot_star_ab(char  * x0) {
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
    int x88;
    if (x16) {
      char  *x17 = x11+1;
      char x18 = x17[0];
      int x19 = x18 == '\0';
      int x22;
      if (x19) {
        x22 = 0/*false*/;
      } else {
        int x21 = 'b' == x18;
        x22 = x21;
      }
      int x87;
      if (x22) {
        int x24 = 0/*false*/;
        int x25 = 1/*true*/;
        char  *x23 = x17+1;
        char  *x26 = x23;
        /*@
        loop invariant ((strlen(x26)>=0) &&
        \valid(x26+(0..strlen(x26))));
        loop assigns x24, x25, x26;
        loop variant ((strlen(x26)+((x24) ? (0) : (1)))+((x25) ? (1) : (0)));
        */
        for (;;) {
          int x27 = x24;
          int x31;
          if (x27) {
            x31 = 0/*false*/;
          } else {
            int x29 = x25;
            x31 = x29;
          }
          if (!x31) break;
          char  *x33 = x26;
          char x34 = x33[0];
          int x35 = x34 == '\0';
          int x38;
          if (x35) {
            x38 = 0/*false*/;
          } else {
            int x37 = 'a' == x34;
            x38 = x37;
          }
          int x47;
          if (x38) {
            char  *x39 = x33+1;
            char x40 = x39[0];
            int x41 = x40 == '\0';
            int x44;
            if (x41) {
              x44 = 0/*false*/;
            } else {
              int x43 = 'b' == x40;
              x44 = x43;
            }
            int x46;
            if (x44) {
              x46 = 1/*true*/;
            } else {
              x46 = 0/*false*/;
            }
            x47 = x46;
          } else {
            x47 = 0/*false*/;
          }
          x24 = x47;
          int x49 = x24;
          if (x49) {
          } else {
            int x36 = !x35;
            x25 = x36;
            int x52 = x25;
            if (x52) {
              x25 = 1/*true*/;
              char  *x39 = x33+1;
              x26 = x39;
            } else {
            }
          }
        }
        int x85 = x24;
        x87 = x85;
      } else {
        x87 = 0/*false*/;
      }
      x88 = x87;
    } else {
      x88 = 0/*false*/;
    }
    x2 = x88;
    int x90 = x2;
    if (x90) {
    } else {
      int x14 = !x13;
      x3 = x14;
      int x93 = x3;
      if (x93) {
        char  *x17 = x11+1;
        x4 = x17;
      } else {
      }
    }
  }
  int x124 = x2;
  return x124;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input matching 'abab'
void test_case_1() {
    char x0[] = "abab";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid input with 'ab' followed by any characters and ending with 'ab'
void test_case_2() {
    char x0[] = "abxab";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid input with 'ab' followed by numbers and ending with 'ab'
void test_case_3() {
    char x0[] = "ab123ab";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid input where first 'a' is not followed by 'b'
void test_case_4() {
    char x0[] = "aab";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid input with only 'ab' but no subsequent 'ab'
void test_case_5() {
    char x0[] = "ab";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - empty string
void test_case_6() {
    char x0[] = "";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - single character string
void test_case_7() {
    char x0[] = "a";
    int result = matcher_ab_dot_star_ab(x0);
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    int result = matcher_ab_dot_star_ab(NULL);  // Frama-C should flag this
}

// Test case 9: Invalid - non-null-terminated string
void test_case_9() {
    char x0[] = {'a', 'b'};  // Not null-terminated
    int result = matcher_ab_dot_star_ab(x0);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_matcher_ab_dot_star_ab() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called - for precondition testing
}
void test_case_8() {
    int result = matcher_ab_dot_star_ab(NULL);
}

void test_case_9() {
    char *invalid = (char*)0xDEADBEEF;
    int result = matcher_ab_dot_star_ab(invalid);
}
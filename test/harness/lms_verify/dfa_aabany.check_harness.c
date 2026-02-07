// ========== Original Code (with ACSL) ==========
/*@ requires strlen(input)>=0 && \valid(input+(0..strlen(input)));
    assigns \nothing;
    ensures \result==0 || \result==1;
*/
int dfa_aabany(char* input) {
  if (*input == '\0') return 0/*false*/;
  int id = 0;
  char c;
  /*@
  loop invariant strlen(input)>0 && \valid(input+(0..strlen(input)));
  loop invariant id == 17 || id == 14 || id == 11 || id == 6 || id == 3 || id == 0;
  loop assigns id, c, input;
  loop variant strlen(input);
  */
  while (input[1] != '\0') {
    c = *input++;
    if (id == 17) {
      char x18 = c;
      int x19 = x18 == 'A';
      int x23;
      if (x19) {
        return 1/*true*/;
      } else {
        return 1/*true*/;
      }
      id = x23;
    }
    else if (id == 14) {
      char x15 = c;
      int x16 = x15 == 'A';
      int x24;
      if (x16) {
        return 1/*true*/;
      } else {
        return 1/*true*/;
      }
      id = x24;
    }
    else if (id == 11) {
      char x12 = c;
      int x13 = x12 == 'A';
      int x26;
      if (x13) {
        return 1/*true*/;
      } else {
        return 1/*true*/;
      }
      id = x26;
    }
    else if (id == 6) {
      char x7 = c;
      int x8 = x7 == 'A';
      int x29;
      if (x8) {
        x29 = 6;
      } else {
        int x10 = x7 == 'B';
        int x28;
        if (x10) {
          return 1/*true*/;
        } else {
          x28 = 0;
        }
        x29 = x28;
      }
      id = x29;
    }
    else if (id == 3) {
      char x4 = c;
      int x5 = x4 == 'A';
      int x30;
      if (x5) {
        x30 = 6;
      } else {
        x30 = 0;
      }
      id = x30;
    }
    else if (id == 0) {
      char x1 = c;
      int x2 = x1 == 'A';
      int x32;
      if (x2) {
        x32 = 3;
      } else {
        x32 = 0;
      }
      id = x32;
    }
    else { return -1; /*error: invalid state*/ }
  }
  c = *input;
  if (id == 17) {
    char x18 = c;
    int x19 = x18 == 'A';
    int x23;
    if (x19) {
      x23 = 1/*true*/;
    } else {
      x23 = 1/*true*/;
    }
    id = x23;
  }
  else if (id == 14) {
    char x15 = c;
    int x16 = x15 == 'A';
    int x24;
    if (x16) {
      x24 = 1/*true*/;
    } else {
      x24 = 1/*true*/;
    }
    id = x24;
  }
  else if (id == 11) {
    char x12 = c;
    int x13 = x12 == 'A';
    int x26;
    if (x13) {
      x26 = 1/*true*/;
    } else {
      x26 = 1/*true*/;
    }
    id = x26;
  }
  else if (id == 6) {
    char x7 = c;
    int x8 = x7 == 'A';
    int x29;
    if (x8) {
      x29 = 0/*false*/;
    } else {
      int x10 = x7 == 'B';
      int x28;
      if (x10) {
        x28 = 1/*true*/;
      } else {
        x28 = 0/*false*/;
      }
      x29 = x28;
    }
    id = x29;
  }
  else if (id == 3) {
    char x4 = c;
    int x5 = x4 == 'A';
    int x30;
    if (x5) {
      x30 = 0/*false*/;
    } else {
      x30 = 0/*false*/;
    }
    id = x30;
  }
  else if (id == 0) {
    char x1 = c;
    int x2 = x1 == 'A';
    int x32;
    if (x2) {
      x32 = 0/*false*/;
    } else {
      x32 = 0/*false*/;
    }
    id = x32;
  }
  else { return -1; /*error: invalid state */ }
  return id;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - "AAB"
void test_case_1() {
    int result = dfa_aabany("AAB");
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - "BAAB"
void test_case_2() {
    int result = dfa_aabany("BAAB");
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - "AA"
void test_case_3() {
    int result = dfa_aabany("AA");
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - "AABB"
void test_case_4() {
    int result = dfa_aabany("AABB");
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - "B"
void test_case_5() {
    int result = dfa_aabany("B");
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - empty string
void test_case_6() {
    int result = dfa_aabany("");
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - single character 'A'
void test_case_7() {
    int result = dfa_aabany("A");
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    int result = dfa_aabany(NULL);  // Frama-C should flag this
}

// Test case 9: Invalid - non-null-terminated string
void test_case_9() {
    char invalid_str[] = {'A', 'A'};
    int result = dfa_aabany(invalid_str);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_dfa_aabany() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called
}
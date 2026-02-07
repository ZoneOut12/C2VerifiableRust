// ========== Original Code (with ACSL) ==========
#include <string.h>
/*@
requires strlen(input)>=0 && \valid(input+(0..strlen(input)));
assigns \nothing;
ensures \result==0 || \result==1;
*/
int dfa_aab(char* input) {
  if (*input == '\0') return 0/*false*/;
  int id = 0;
  char c;
  /*@
  loop invariant strlen(input)>0 && \valid(input+(0..strlen(input)));
  loop invariant id == 6 || id == 3 || id == 0;
  loop assigns id, c, input;
  loop variant strlen(input);
  */
  while (input[1] != '\0') {
    c = *input++;
    if (id == 0) {
      char x1 = c;
      int x2 = x1 == 'A';
      int x16;
      if (x2) {
        x16 = 3;
      } else {
        x16 = 0;
      }
      id = x16;
    }
    else if (id == 6) {
      char x7 = c;
      int x8 = x7 == 'A';
      int x13;
      if (x8) {
        x13 = 6;
      } else {
        x13 = 0;
      }
      id = x13;
    }
    else if (id == 3) {
      char x4 = c;
      int x5 = x4 == 'A';
      int x14;
      if (x5) {
        x14 = 6;
      } else {
        x14 = 0;
      }
      id = x14;
    }
    else { return -1; /*error: invalid state*/ }
  }
  c = *input;
  if (id == 0) {
    char x1 = c;
    int x2 = x1 == 'A';
    int x16;
    if (x2) {
      x16 = 0/*false*/;
    } else {
      x16 = 0/*false*/;
    }
    id = x16;
  }
  else if (id == 6) {
    char x7 = c;
    int x8 = x7 == 'A';
    int x13;
    if (x8) {
      x13 = 0/*false*/;
    } else {
      x13 = 1/*true*/;
    }
    id = x13;
  }
  else if (id == 3) {
    char x4 = c;
    int x5 = x4 == 'A';
    int x14;
    if (x5) {
      x14 = 0/*false*/;
    } else {
      x14 = 0/*false*/;
    }
    id = x14;
  }
  else { return -1; /*error: invalid state */ }
  return id;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input "AAB"
void test_case_1() {
    char input[] = "AAB";
    int result = dfa_aab(input);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid input "AAAAB"
void test_case_2() {
    char input[] = "AAAAB";
    int result = dfa_aab(input);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid input "A"
void test_case_3() {
    char input[] = "A";
    int result = dfa_aab(input);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid input "B"
void test_case_4() {
    char input[] = "B";
    int result = dfa_aab(input);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid input "AA"
void test_case_5() {
    char input[] = "AA";
    int result = dfa_aab(input);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary case empty string
void test_case_6() {
    char input[] = "";
    int result = dfa_aab(input);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary case "AB"
void test_case_7() {
    char input[] = "AB";
    int result = dfa_aab(input);
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid NULL pointer
void test_case_8() {
    char* input = NULL;
    int result = dfa_aab(input);  // Frama-C should flag this
}

// Test case 9: Invalid non-null-terminated array
void test_case_9() {
    char arr[2] = {'A', 'B'};
    int result = dfa_aab(arr);  // Frama-C should flag this
}

// Harness entry point
void test_harness_dfa_aab() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called - for precondition testing
}
// ========== Original Code (with ACSL) ==========
/*@ requires strlen(a)>=0 && \\valid(a+(0..strlen(a)));
    assigns \\nothing;
    ensures 0<=\\result || \\result==-1;
 */
int my_atoi(char* a) {
  int m = INT_MAX/10 - 10;
  int r = 0;
  char* s = a;
  /*@
    loop invariant strlen(s)>=0 && \\valid(s+(0..strlen(s)));
    loop invariant 0 <= r;
    loop assigns r, s;
    loop variant strlen(s);
  */
  while ('0' <= *s && *s <= '9') {
    if (r > m) return -1;
    r = 10*r + (*s - '0');
    s++;
  }
  return r;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input with normal number
void test_case_1() {
    char a[] = "123";
    int result = my_atoi(a);
    printf("test_case_1: %d\\n", result);
}

// Test case 2: Valid input zero
void test_case_2() {
    char a[] = "0";
    int result = my_atoi(a);
    printf("test_case_2: %d\\n", result);
}

// Test case 3: Valid input digits followed by non-digits
void test_case_3() {
    char a[] = "456abc";
    int result = my_atoi(a);
    printf("test_case_3: %d\\n", result);
}

// Test case 4: Valid input leading zeros
void test_case_4() {
    char a[] = "0042";
    int result = my_atoi(a);
    printf("test_case_4: %d\\n", result);
}

// Test case 5: Valid single digit
void test_case_5() {
    char a[] = "7";
    int result = my_atoi(a);
    printf("test_case_5: %d\\n", result);
}

// Test case 6: Boundary empty string
void test_case_6() {
    char a[] = "";
    int result = my_atoi(a);
    printf("test_case_6: %d\\n", result);
}

// Test case 7: Boundary input at overflow threshold
void test_case_7() {
    char a[] = "214748354";
    int result = my_atoi(a);
    printf("test_case_7: %d\\n", result);
}

// Test case 8: Invalid NULL pointer
void test_case_8() {
    char* a = NULL;
    int result = my_atoi(a);
}

// Test case 9: Invalid non-null-terminated array
void test_case_9() {
    char a[2] = {'1','2'};
    int result = my_atoi(a);
}

void test_harness_my_atoi() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and 9 intentionally not called - for precondition testing
}
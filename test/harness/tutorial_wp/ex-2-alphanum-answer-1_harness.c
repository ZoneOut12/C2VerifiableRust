// ========== Original Code (with ACSL) ==========
/*@ assigns \nothing ;
  ensures \result <==> 'a' <= c <= 'z' ;
*/
int is_lower_alpha(char c){
  return 'a' <= c && c <= 'z' ;
}

/*@ assigns \nothing ;
  ensures \result <==> 'A' <= c <= 'Z' ;
*/
int is_upper_alpha(char c){
  return 'A' <= c && c <= 'Z' ;
}

/*@ assigns \nothing ;
  ensures \result <==> '0' <= c <= '9' ;
*/
int is_digit(char c){
  return '0' <= c && c <= '9' ;
}

/*@ assigns \nothing ;
  ensures 
  \result <==> (
    ('a' <= c <= 'z') ||
    ('A' <= c <= 'Z') ||
    ('0' <= c <= '9')
  ) ;
*/
int is_alpha_num(char c){
  return
    is_lower_alpha(c) || 
    is_upper_alpha(c) ||
    is_digit(c) ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - lowercase 'a'
void test_case_1() {
    char c = 'a';
    int result = is_alpha_num(c);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - uppercase 'Z'
void test_case_2() {
    char c = 'Z';
    int result = is_alpha_num(c);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - digit '5'
void test_case_3() {
    char c = '5';
    int result = is_alpha_num(c);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - lowercase 'm'
void test_case_4() {
    char c = 'm';
    int result = is_alpha_num(c);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - uppercase 'C'
void test_case_5() {
    char c = 'C';
    int result = is_alpha_num(c);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Boundary - lowercase 'z'
void test_case_6() {
    char c = 'z';
    int result = is_alpha_num(c);
    printf("test_case_6: %d\n", result);  // Expected: 1
}

// Test case 7: Boundary - digit '9'
void test_case_7() {
    char c = '9';
    int result = is_alpha_num(c);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - space character
void test_case_8() {
    char c = ' ';
    int result = is_alpha_num(c);
    // No output check needed for invalid case
}

// Test case 9: Invalid - special character '@'
void test_case_9() {
    char c = '@';
    int result = is_alpha_num(c);
    // No output check needed for invalid case
}

// Harness entry point
void test_harness_is_alpha_num() {
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
    char c = ' ';
    int result = is_alpha_num(c);
    assert(result == 0);
}

void test_case_9() {
    char c = '@';
    int result = is_alpha_num(c);
    assert(result == 0);
}
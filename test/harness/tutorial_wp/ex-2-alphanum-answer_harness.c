// ========== Original Code (with ACSL) ==========
enum Kind { LOWER, UPPER, DIGIT, OTHER } ;

/*@
  predicate lower(char c) = 'a' <= c <= 'z' ;
  predicate upper(char c) = 'A' <= c <= 'Z' ;
  predicate digit(char c) = '0' <= c <= '9' ;
*/

/*@
  assigns \nothing ;
  ensures \result <==> lower(c) ;
*/
int is_lower_alpha(char c){
  return 'a' <= c && c <= 'z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> upper(c) ;
*/
int is_upper_alpha(char c){
  return 'A' <= c && c <= 'Z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> digit(c) ;
*/
int is_digit(char c){
  return '0' <= c && c <= '9' ;
}

/*@
  assigns \nothing ;
  behavior lower:
    assumes lower(c);
    ensures \result == LOWER ;

  behavior upper:
    assumes upper(c) ;
    ensures \result == UPPER ;

  behavior digit:
    assumes digit(c) ;
    ensures \result == DIGIT ;

  behavior other:
    assumes !(lower(c) || upper(c) || digit(c)) ;
    ensures \result == OTHER ;

  complete behaviors ;
  disjoint behaviors ;
*/
enum Kind character_kind(char c){
  if(is_lower_alpha(c)) return LOWER ;
  if(is_upper_alpha(c)) return UPPER ;
  if(is_digit(c))       return DIGIT ;
  return OTHER ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - lowercase letter m
void test_case_1() {
    char c = 'm';
    enum Kind result = character_kind(c);
    printf("test_case_1: %d\n", result);  // Expected: 0 (LOWER)
}

// Test case 2: Valid - uppercase letter T
void test_case_2() {
    char c = 'T';
    enum Kind result = character_kind(c);
    printf("test_case_2: %d\n", result);  // Expected: 1 (UPPER)
}

// Test case 3: Valid - digit 7
void test_case_3() {
    char c = '7';
    enum Kind result = character_kind(c);
    printf("test_case_3: %d\n", result);  // Expected: 2 (DIGIT)
}

// Test case 4: Valid - space character
void test_case_4() {
    char c = ' ';
    enum Kind result = character_kind(c);
    printf("test_case_4: %d\n", result);  // Expected: 3 (OTHER)
}

// Test case 5: Valid - special character @
void test_case_5() {
    char c = '@';
    enum Kind result = character_kind(c);
    printf("test_case_5: %d\n", result);  // Expected: 3 (OTHER)
}

// Test case 6: Boundary - lowercase boundary a
void test_case_6() {
    char c = 'a';
    enum Kind result = character_kind(c);
    printf("test_case_6: %d\n", result);  // Expected: 0 (LOWER)
}

// Test case 7: Boundary - uppercase boundary Z
void test_case_7() {
    char c = 'Z';
    enum Kind result = character_kind(c);
    printf("test_case_7: %d\n", result);  // Expected: 1 (UPPER)
}

// Test case 8: Invalid - negative char
void test_case_8() {
    char c = -1;
    enum Kind result = character_kind(c);
    // No output check needed for invalid case
}

// Test case 9: Invalid - char beyond 7-bit ASCII
void test_case_9() {
    char c = 128;
    enum Kind result = character_kind(c);
    // No output check needed for invalid case
}

// Harness entry point (not main!)
void test_harness_character_kind() {
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
    assert(character_kind('a') == KIND_LETTER);
}

void test_case_9() {
    assert(character_kind('5') == KIND_DIGIT);
}
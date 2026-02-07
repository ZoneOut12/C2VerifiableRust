// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ predicate is_pos(int  x0) = (x0>0);*/
/*@
assigns \nothing;
ensures \result <==> is_pos(x0);
*/
int is_pos(int  x0) {
  int x2 = x0 > 0;
  return x2;
}
/*@ predicate is_nat(int  x3) = (x3>=0);*/
/*@
assigns \nothing;
ensures \result <==> is_nat(x3);
*/
int is_nat(int  x3) {
  int x5 = x3 >= 0;
  return x5;
}
/*@
requires is_pos(x6);
assigns \nothing;
ensures is_nat(\result);
*/
int minus1(int  x6) {
  int x8 = x6 - 1;
  return x8;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <assert.h>

// --- Tests for is_pos ---
void test_is_pos_valid() {
    printf("Running test_is_pos...\n");
    assert(is_pos(1) == 1);          // 1. Minimum positive
    assert(is_pos(100) == 1);        // 2. Typical positive
    assert(is_pos(INT_MAX) == 1);    // 3. Maximum boundary
    assert(is_pos(0) == 0);          // 4. Zero (not positive)
    assert(is_pos(-1) == 0);         // 5. Negative boundary
    assert(is_pos(-100) == 0);       // 6. Typical negative
    assert(is_pos(INT_MIN) == 0);    // 7. Minimum boundary
}

// is_pos has no 'requires' clause, so theoretically all ints are valid inputs.
// We treat logic errors as the "invalid" context here.
void test_is_pos_invalid() {
    // No specific invalid cases for is_pos under the current ACSL contract.
}

// --- Tests for is_nat ---
void test_is_nat_valid() {
    printf("Running test_is_nat...\n");
    assert(is_nat(0) == 1);          // 1. Minimum natural number
    assert(is_nat(1) == 1);          // 2. Positive integer
    assert(is_nat(INT_MAX) == 1);    // 3. Maximum boundary
    assert(is_nat(-1) == 0);         // 4. Negative boundary
    assert(is_nat(-50) == 0);        // 5. Typical negative
    assert(is_nat(INT_MIN) == 0);    // 6. Minimum boundary
    assert(is_nat(42) == 1);         // 7. Arbitrary natural number
}

// is_nat has no 'requires' clause.
void test_is_nat_invalid() {
    // No specific invalid cases for is_nat under the current ACSL contract.
}

// --- Tests for minus1 ---
void test_minus1_valid() {
    printf("Running test_minus1_valid...\n");
    assert(minus1(1) == 0);          // 1. Boundary: 1 -> 0
    assert(minus1(2) == 1);          // 2.
    assert(minus1(10) == 9);         // 3.
    assert(minus1(100) == 99);       // 4.
    assert(minus1(INT_MAX) == INT_MAX - 1); // 5. Max boundary
    assert(minus1(50) == 49);        // 6.
    assert(minus1(999) == 998);      // 7.
}

/* Invalid cases for minus1: These violate the 'requires is_pos(x6)' clause.
  Calling these would result in undefined behavior or contract failure in Frama-C.
*/
void test_minus1_invalid() {
    // 8. Invalid: Input 0 violates is_pos
    // int res = minus1(0); 
    
    // 9. Invalid: Input negative violates is_pos
    // int res = minus1(-5);
}
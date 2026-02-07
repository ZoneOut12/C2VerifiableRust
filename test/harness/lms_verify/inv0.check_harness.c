#include <limits.h>
/*@ predicate inv_vec_Int(int* x0, integer  x1) = ((x1==0) || ((x1>0) &&
\valid(x0+(0..x1-1))));*/
/*@ predicate eq_vec_Int(int* x15, int  x16, int* x17, int  x18) = ((x16==x18) &&
(\forall int x22; (0<=x22<x16) ==> (x15[x22]==x17[x22])));*/
/*@
requires (inv_vec_Int(x15,x16) &&
inv_vec_Int(x17,x18));
assigns \nothing;
ensures (inv_vec_Int(x15,x16) &&
inv_vec_Int(x17,x18));
ensures \result <==> eq_vec_Int(x15, x16, x17, x18);
*/
int eq_vec_Int(int  * x15, int  x16, int  * x17, int  x18) {
  int x20 = x16 == x18;
  int x31;
  if (x20) {
    int x30 = 1;
    /*@ loop invariant (0 <= x23 <= x16);
    loop invariant \forall int x22; (0 <= x22 < x23) ==> (x15[x22]==x17[x22]);
    loop invariant x30==1;
    loop assigns x23, x30;
    loop variant (x16-x23); */
    for (int x23 = 0; x23 < x16; x23++) {
      int x27 = x15[x23];
      int x28 = x17[x23];
      int x29 = x27 == x28;
      if (!x29) { x30 = 0; break; }
    }
    x31 = x30;
  } else {
    x31 = 0/*false*/;
  }
  return x31;
}

// ========== Main Test Entry ==========

void test_harness_eq_vec_Int() {
    // Test case 1: Identical arrays
    int v1_t1[] = {1, 2, 3};
    int v2_t1[] = {1, 2, 3};
    int res1 = eq_vec_Int(v1_t1, 3, v2_t1, 3);
    printf("test_case_1: result=%d (Expected: 1)\n", res1);

    // Test case 2: Different lengths
    int v1_t2[] = {1, 2, 3};
    int v2_t2[] = {1, 2};
    int res2 = eq_vec_Int(v1_t2, 3, v2_t2, 2);
    printf("test_case_2: result=%d (Expected: 0)\n", res2);

    // Test case 3: Same length, different values
    int v1_t3[] = {1, 2, 3};
    int v2_t3[] = {1, 5, 3};
    int res3 = eq_vec_Int(v1_t3, 3, v2_t3, 3);
    printf("test_case_3: result=%d (Expected: 0)\n", res3);

    // Test case 4: Single element match
    int v1_t4[] = {42};
    int v2_t4[] = {42};
    int res4 = eq_vec_Int(v1_t4, 1, v2_t4, 1);
    printf("test_case_4: result=%d (Expected: 1)\n", res4);

    // Test case 5: Large/Small integer boundaries
    int v1_t5[] = {INT_MAX, INT_MIN};
    int v2_t5[] = {INT_MAX, INT_MIN};
    int res5 = eq_vec_Int(v1_t5, 2, v2_t5, 2);
    printf("test_case_5: result=%d (Expected: 1)\n", res5);

    // Test case 6: Empty arrays (Size 0)
    int res6 = eq_vec_Int(NULL, 0, NULL, 0);
    printf("test_case_6: result=%d (Expected: 1)\n", res6);

    // Test case 7: Mismatch on last element
    int v1_t7[] = {10, 20, 30};
    int v2_t7[] = {10, 20, 31};
    int res7 = eq_vec_Int(v1_t7, 3, v2_t7, 3);
    printf("test_case_7: result=%d (Expected: 0)\n", res7);

    eq_vec_Int(NULL, 5, NULL, 5);
}

// Test case 8: Invalid - buffer smaller than specified size
void test_case_8() {
    int v1_err[] = {}; // Empty array (size 0)
    int v2_err[] = {1, 2};
    
    // In Rust: CheckPre_eq_vec_Int(&v1_err, 5, &v2_err, 2);
    // In C, this is a violation of the ACSL: \valid(x0 + (0..x1-1))
    // because x0 is size 0, but we tell the function to read 5 elements.
    int res = eq_vec_Int(v1_err, 5, v2_err, 2);
    
    printf("test_case_8: result=%d (Expected: ACSL violation/Invalid Access)\n", res);
}
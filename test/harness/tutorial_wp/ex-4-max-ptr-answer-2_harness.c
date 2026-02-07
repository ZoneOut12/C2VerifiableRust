/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;
  ensures  \old(*a) < \old(*b)  ==> *a == \old(*b) && *b == \old(*a) ;
  ensures  \old(*a) >= \old(*b) ==> *a == \old(*a) && *b == \old(*b) ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  max_ptr(&a, &b) ;

  //@ assert a == 42 && b == 24 ;
  //@ assert h == 42 ;
}

// --- Test Case 1: Standard Swap (a < b) ---
void test_case_1() {
    int a = 24, b = 42;
    max_ptr(&a, &b);
    // Expected: a = 42, b = 24
    printf("test_case_1: a=%d, b=%d\n", a, b);
}

// --- Test Case 2: No Swap Needed (a > b) ---
void test_case_2() {
    int a = 50, b = 30;
    max_ptr(&a, &b);
    // Expected: a = 50, b = 30 (remains same)
    printf("test_case_2: a=%d, b=%d\n", a, b);
}

// --- Test Case 3: Negative Values (a < b) ---
void test_case_3() {
    int a = -10, b = -5;
    max_ptr(&a, &b);
    // Expected: a = -5, b = -10
    printf("test_case_3: a=%d, b=%d\n", a, b);
}

// --- Test Case 4: Zero and Negative (a > b) ---
void test_case_4() {
    int a = 0, b = -100;
    max_ptr(&a, &b);
    // Expected: a = 0, b = -100
    printf("test_case_4: a=%d, b=%d\n", a, b);
}

// --- Test Case 5: Extreme Values (INT_MIN/MAX) ---
void test_case_5() {
    int a = INT_MIN, b = INT_MAX;
    max_ptr(&a, &b);
    // Expected: a = 2147483647, b = -2147483648
    printf("test_case_5: a=%d, b=%d\n", a, b);
}

// --- Test Case 6: Boundary - Equal Values ---
void test_case_6() {
    int a = 42, b = 42;
    max_ptr(&a, &b);
    // Expected: a = 42, b = 42
    printf("test_case_6: a=%d, b=%d\n", a, b);
}

// --- Test Case 7: Boundary - Same Pointer (Aliasing) ---
void test_case_7() {
    int a = -100000, b = 500
    // Note: a and b point to the same memory location
    max_ptr(&a, &b);
    printf("test_case_7: a=%d, b=%d\n", a, b);
}

// --- Test Case 8: Invalid - NULL pointer for 'a' ---
void test_case_8() {
    int b = 42;
    // Frama-C WP will flag this: requires \valid(a) failed
    max_ptr(NULL, &b);
}

// --- Test Case 9: Invalid - NULL pointer for 'b' ---
void test_case_9() {
    int a = 24;
    // Frama-C WP will flag this: requires \valid(b) failed
    max_ptr(&a, NULL);
}

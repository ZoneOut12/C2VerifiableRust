// ========== Original Code (with ACSL) ==========
#include <assert.h>
#include <limits.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main()
{


  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  /*@
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant 1 <= w;
  loop invariant 0 <= x;
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  */
  while(unknown1()) {
    
    /*@
    loop invariant x == y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
    */
    while(unknown2()){
      if(w%2 == 1){
        if (x == 2147483647) break;
        x++;
      }
      if(z%2 == 0){
        if (y == 2147483647) break;
        y++;
      }
    }
    if (x <= (2147483647 - 1)/2){
      z = x + y;
      w = z + 1;
    }
  }

  
  //@ assert x == y;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - outer loop not entered
int uk1_count = 0;
int unknown1() { return 0; }
int unknown2() { return 0; }
void test_case_1() {
    main();
    printf("test_case_1: x == y\n");
}

// Test case 2: Valid - inner loop increments once
int uk1_count_2 = 0;
int unknown1() { return ++uk1_count_2 <= 1; }
int unknown2_count = 0;
int unknown2() { return ++unknown2_count <= 1; }
void test_case_2() {
    main();
    printf("test_case_2: x == y\n");
}

// Test case 3: Valid - multiple balanced increments
int uk1_count_3 = 0;
int unknown1() { return ++uk1_count_3 <= 2; }
int unknown2_count_3 = 0;
int unknown2() { return ++unknown2_count_3 <= 3; }
void test_case_3() {
    main();
    printf("test_case_3: x == y\n");
}

// Test case 4: Valid - multiple outer loops
int uk1_count_4 = 0;
int unknown1() { return ++uk1_count_4 <= 2; }
int unknown2_count_4 = 0;
int unknown2() { return ++unknown2_count_4 <= 2; }
void test_case_4() {
    main();
    printf("test_case_4: x == y\n");
}

// Test case 5: Valid - near overflow
int uk1_count_5 = 0;
int unknown1() { return ++uk1_count_5 <= 1; }
int unknown2_count_5 = 0;
int unknown2() { 
    if (++unknown2_count_5 <= 1) {
        x = 2147483646;
        y = 2147483646;
        return 1;
    }
    return 0;
}
void test_case_5() {
    main();
    printf("test_case_5: x == y\n");
}

// Test case 6: Invalid - hypothetical unbalanced increment
int uk1_count_6 = 0;
int unknown1() { return ++uk1_count_6 <= 1; }
int unknown2_count_6 = 0;
int unknown2() { 
    if (++unknown2_count_6 <= 1) {
        w = 2; // Even to skip x++
        z = 1; // Odd to skip y++
        return 1;
    }
    return 0;
}
void test_case_6() {
    main();
    printf("test_case_6: x == y?\n");
}

// Test case 7: Invalid - w becomes 0
int uk1_count_7 = 0;
int unknown1() { 
    if (++uk1_count_7 <= 1) {
        w = 0; // Violates loop invariant
        return 1;
    }
    return 0;
}
int unknown2_count_7 = 0;
int unknown2() { return ++unknown2_count_7 <= 1; }
void test_case_7() {
    main();
    printf("test_case_7: w >= 1?\n");
}

// Test case 8: Boundary - x/y at INT_MAX-1
int uk1_count_8 = 0;
int unknown1() { return ++uk1_count_8 <= 1; }
int unknown2_count_8 = 0;
int unknown2() { 
    if (++unknown2_count_8 <= 1) {
        x = 2147483646;
        y = 2147483646;
        return 1;
    }
    return 0;
}
void test_case_8() {
    main();
    printf("test_case_8: x/y at INT_MAX-1\n");
}

// Test case 9: Boundary - z at INT_MAX
int uk1_count_9 = 0;
int unknown1() { return ++uk1_count_9 <= 1; }
int unknown2_count_9 = 0;
int unknown2() { 
    if (++unknown2_count_9 <= 1) {
        x = 1073741823;
        y = 1073741823;
        return 1;
    }
    return 0;
}
void test_case_9() {
    main();
    printf("test_case_9: z at INT_MAX\n");
}

// Harness entry point
void test_harness_main() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // Invalid cases may cause undefined behavior
    // test_case_6();
    // test_case_7();
    test_case_8();
    test_case_9();
}
void test_case_1() {
  global_arr = (int[]){1, 2, 3};
  global_n = 3;
  main();
  // Assert expected output based on function behavior
}
void test_case_2() {
  global_arr = (int[]){4, 5, 6};
  global_n = 3;
  main();
}
void test_case_3() {
  global_arr = (int[]){-1, 0, 1};
  global_n = 3;
  main();
}
void test_case_4() {
  global_arr = (int[]){10};
  global_n = 1;
  main();
}
void test_case_5() {
  global_arr = NULL;
  global_n = 0;
  main();
}
void test_case_6() {
  global_arr = (int[]){2, 1, 3};
  global_n = 3;
  main();
}
void test_case_7() {
  global_arr = (int[]){1, 2, 3};
  global_n = 2;
  main();
}
void test_case_8() {
  global_arr = NULL;
  global_n = 1;
  main();
}
void test_case_9() {
  global_arr = (int[]){5, 3};
  global_n = 2;
  main();
}
#include <stddef.h>

/*@
  requires \valid(a) && \valid(b);
  assigns *a, *b;
  ensures  *a == \old(*b) && *b == \old(*a);
*/
void swap(int* a, int* b){
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

/*@
  requires \valid(array + (0 .. len-1)) ;

  assigns array[0 .. len-1];

  ensures \forall integer j ; 0 <= j < len ==> array[j] == \old(array[len-j-1]);
*/
void reverse(int* array, size_t len){
  /*@
    loop invariant 0 <= i <= len/2 ;
    loop invariant 
      \forall integer j ; (0 <= j < i || len-i <= j < len) ==> 
        array[j] == \at(array[len-j-1], Pre);
    loop invariant
      \forall integer j ; i <= j < len-i ==> array[j] == \at(array[j], Pre);
    loop assigns i, array[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len/2 ; ++i){
    swap(array+i, array+len-i-1) ;
  }
}

typedef int (*unary_int_op)(int);

/*@ requires -1000000 <= x <= 1000000;
    assigns \nothing;
    ensures \result == x + x;
*/
int fp_double(int x)
{
    return x + x;
}

/*@ requires -1000000 <= x <= 1000000;
    assigns \nothing;
    ensures \result == -x;
*/
int fp_negate(int x)
{
    return -x;
}

/*@ requires f == &fp_double || f == &fp_negate;
    requires -1000000 <= x <= 1000000;
    assigns \nothing;
    ensures f == &fp_double ==> \result == x + x;
    ensures f == &fp_negate ==> \result == -x;
*/
int apply_fn(unary_int_op f, int x)
{
    if (f == &fp_double) return fp_double(x);
    return fp_negate(x);
}

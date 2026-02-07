#include <limits.h>
#include <stddef.h>

/*@
  axiomatic Sum_array{
    logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
   
    axiom empty: 
      \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
    axiom range:
      \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1)+a[e-1];
  }
*/

/*@
  predicate unchanged{L1, L2}(int* array, integer begin, integer end) =
    \forall integer i ; begin <= i < end ==> \at(array[i], L1) == \at(array[i], L2) ;
*/

/*@
  requires begin <= split <= end ;
  assigns  \nothing ;
  ensures  sum(array, begin, end) == sum(array, begin, split) + sum(array, split, end) ;
*/
void sum_separable(int* array, size_t begin, size_t split, size_t end){
  /*@
    loop invariant split <= i <= end ;
    loop invariant 
      sum(array, begin, i) == sum(array, begin, split) + sum(array, split, i) ;
    loop assigns i ;
    loop variant end - i ;
  */
  for(size_t i = split ; i < end ; ++i);
}  

/*@
  requires i < len ;
  requires array[i] < INT_MAX ;
  requires \valid(array + (0 .. len-1));
  assigns array[i];
  ensures sum(array, 0, len) == sum{Pre}(array, 0, len)+1;
*/
void inc_cell(int* array, size_t len, size_t i){
  sum_separable(array, 0, i, len);
  sum_separable(array, i, i+1, len);
  array[i]++ ;
  sum_separable(array, 0, i, len);
  sum_separable(array, i, i+1, len);
  
  //@ assert unchanged{Pre, Here}(array, 0, i) ;                 
  /*@ 
     loop invariant 0 <= _i <= i ;                                
     loop invariant sum{Pre}(array, 0, _i) ==                         
                    sum{Here}(array, 0, _i) ;                          
     loop assigns _i ;                                                  
     loop variant i - _i ;                                          
  */                                                                   
  for(size_t _i = 0 ; _i < i ; ++_i) ;                            
  //@ assert sum{Pre}(array, 0, i) == sum{Here}(array, 0, i) ;
  
  //@ assert unchanged{Pre, Here}(array, i+1, len) ;                 
  /*@ 
     loop invariant i+1 <= _i <= len ;                                
     loop invariant sum{Pre}(array, i+1, _i) ==                         
                    sum{Here}(array, i+1, _i) ;                          
     loop assigns _i ;                                                  
     loop variant len - _i ;                                          
  */                                                                   
  for(size_t _i = i+1 ; _i < len ; ++_i) ;                            
  //@ assert sum{Pre}(array, i+1, len) == sum{Here}(array, i+1, len) ;
  
  // ghost unchanged_sum(Pre, Here, array, 0, i);
  // ghost unchanged_sum(Pre, Here, array, i+1, len);
}

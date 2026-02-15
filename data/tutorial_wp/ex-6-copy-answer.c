#include <stddef.h>

/*@
  requires \valid_read(src + (0 .. len-1));
  requires \valid(dst + (0 .. len-1));
  requires \separated(&src[0 .. len-1], &dst[0 .. len-1]) ;

  assigns dst[0 .. len-1];

  ensures \forall integer j ; 0 <= j < len ==> \old(src[j]) == dst[j] ;
*/
void first_copy(int const* src, int* dst, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> \at(src[j], Pre) == dst[j] ;
    loop invariant \forall integer j ; i <= j < len ==> \at(src[j], Pre) == src[j] ;
    loop assigns i, dst[0 .. len-1] ;
    loop variant len - i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    dst[i] = src[i];
  }
}

/*@
  requires \valid_read(src + (0 .. len-1));
  requires \valid(dst + (0 .. len-1));
  requires \separated(&src[0 .. len-1], dst) ;

  assigns dst[0 .. len-1];

  ensures \forall integer j ; 0 <= j < len ==> \old(src[j]) == dst[j] ;
*/
void copy(int const* src, int* dst, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; 0 <= j < i ==> \at(src[j], Pre) == dst[j] ;
    loop invariant \forall integer j ; i <= j < len ==> \at(src[j], Pre) == src[j] ;
    loop assigns i, dst[0 .. len-1] ;
    loop variant len - i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    dst[i] = src[i];
  }
}

/*@
  requires \valid_read(src + (0 .. len-1));
  requires \valid(dst + (0 .. len-1));
  requires \separated(&src[0 .. len-1], dst + len) ;

  assigns dst[0 .. len-1];

  ensures \forall integer j ; 0 <= j < len ==> \old(src[j]) == dst[j] ;
*/
void copy_backward(int const* src, int* dst, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant \forall integer j ; i <= j < len ==> \at(src[j], Pre) == dst[j] ;
    loop invariant \forall integer j ; 0 <= j < i ==> \at(src[j], Pre) == src[j] ;
    loop assigns i, dst[0 .. len-1] ;
    loop variant i ;
  */
  for(size_t i = len ; i > 0 ; --i){
    dst[i-1] = src[i-1];
  }
}

/*@ requires \valid(pp);
    requires \valid(*pp);
    assigns **pp;
    ensures **pp == val;
*/
void store_indirect(int **pp, int val)
{
    **pp = val;
}

/*@ requires \valid(src_pp);
    requires \valid(dst_pp);
    requires \valid(*src_pp);
    requires \valid(*dst_pp);
    requires \separated(*src_pp, *dst_pp);
    assigns **dst_pp;
    ensures **dst_pp == \old(**src_pp);
*/
void copy_indirect(int **src_pp, int **dst_pp)
{
    **dst_pp = **src_pp;
}

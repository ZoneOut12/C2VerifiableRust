/* run.config
   EXIT: 1
   STDOPT:
*/

/*@
  requires n * 42 <= INT_MAX;    
*/
int sum_42(int n){
  int x = 0 ;
  //@ ghost int r = 42 ;
  /*@
    loop invariant x == i * r;
  */
  for(int i = 0; i < n; ++i){
    x += r;
  }
  return x;
}
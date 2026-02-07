/* run.config
   EXIT: 1
   STDOPT:
*/

//@ ghost int x ;

/*@ ghost
  /@ assigns x ; @/
  void ghost_foo(void);
*/

/*@ assigns x; */
void foo(void){
  /*@ ghost
    /@ loop assigns x, i; @/
    for(int i = 0; i < 10; ++i);
  */
}

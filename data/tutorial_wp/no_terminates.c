unsigned counter ;

/*@ terminates \false;
    ensures \false;
*/
void does_not_terminate(void){
  //@ loop assigns counter ;
  while(1){
    counter++;
  }
}

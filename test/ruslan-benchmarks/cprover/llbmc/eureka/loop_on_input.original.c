#include <llbmc.h>

int main(){
  int x,i;
  x=5;
  x=__llbmc_nondef_int();
  while(x<4){
    if(x>0){
      x=x+1;
    } else {
      x=1;
    }
  }
 L: __llbmc_assert(0);
  return 0;
}

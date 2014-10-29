#include <llbmc.h>

int i;
int a[20];

int main(){
  i=0;
  i=__llbmc_nondef_int();
  if(i>0){
    while(i<20){
      a[i]=i;
      i=i+1;
    }
  } else {
  L: __llbmc_assert(0);
  }
  return 0;
}

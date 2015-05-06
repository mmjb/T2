#include "llbmc.h"

int a[10];
int main(){
  int i,j;

  i=0;
  while(i<10){
    if(i==5){
      i=a[i];
      L: __llbmc_assert(a[i]>0);
    } else {
      j=i;
    }
    i++;
  }
  return 0;
}


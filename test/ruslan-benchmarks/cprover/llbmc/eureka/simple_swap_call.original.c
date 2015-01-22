#include <llbmc.h>

int a[2];
int i,j,tmp;
int main(){
  i=0;
  j=1;
  a[i]=100;
  a[j]=200;
  tmp=a[i];
  a[i]=a[j];
  a[j]=tmp;
  if(a[i]==100){
    __llbmc_assert(0);
  } else {
    ;
  }
  return 0;
}

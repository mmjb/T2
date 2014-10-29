#include "necla.h"

int main(){
   int x,y;
   int a[10];
   x=1U;
   while (x <= 10){
      y=10-x;
      a[y] = -1;
      x++;
   }

   return 1;

}

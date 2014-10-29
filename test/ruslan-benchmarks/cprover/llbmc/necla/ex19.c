#include "necla.h"

/* int __llbmc_main(int i, int j){ */
int main(int i, int j){

   ASSUME (0 <= i);
   ASSUME (i <= 1000);

   int x,y;
   int a[1];
   x=i;
   y=j;

   while (x!=0) {
      x--;
      y--;
   }

   if (i==j){
      ASSERT( y == 0);

      
   }
   
   
   return 1;
}

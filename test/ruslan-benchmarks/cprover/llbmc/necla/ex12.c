#include "necla.h"

int main(){
   int i,j = 0;
   int a[20];
   
   L0: {
      {
         j = j +2;
         i = j+2;
      }
         
      a[i] = 0;

      if ( j < 20)
         goto L0;
      
   }

   return 1;

}

#include "necla.h"

int main(){
   int a[5];
   int len=0;

   int i;


   while(__NONDET__()){
     
      if (len==4)
         len =0;
      
      a[len]=0;

      len++;
   }

   return 1;

   
}

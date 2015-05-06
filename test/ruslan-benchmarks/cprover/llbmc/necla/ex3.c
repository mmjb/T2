#include "necla.h"

int x;

int main(){

   int a[100];
   int i,j=0;
   x=10;
   
   if (x <= 1)
      return 1;
   
   for (i =0; i< x ; ++i){
      j = j +2;
   }

   if ( j >= 2*x)   {
      a[101]=0; /*-- force an error here! --*/
   }
   
   return j;

}



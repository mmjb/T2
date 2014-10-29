#include "necla.h"

int a[5];

int foo (int x, int y){
   int i=0;
   
   if (x==y) return x ;

  
   while (i <= x){
      if (x > 0)
         y = y+ x;
   }
   
   
   return y;
}

int main(){

   int i = foo(3,3);

   int j = foo(-3, 4);

   int k = foo(3, -6);

   if ( i > 4){
      a[5] =1;
   }


   return i;
   
}

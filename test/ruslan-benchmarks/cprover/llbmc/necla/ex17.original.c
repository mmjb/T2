#include "necla.h"
#include <stdlib.h>

int a[200];


int check(int * a, int j){

   int * b;
   
   for (b=a; b < a + 100 ; ++b){

      if (*b)
         j = j +1;
   }
   

   return j;
}

int main(){

   int i,j;
   int * b;
   
   for (i=0; i< 100; ++i){
      a[i]=j;
   }

   j=i-2;

  
   if (i >= 0) return 1;

   j = check(a,j);
   b= (int *) malloc(100 * sizeof(int));

   if (b != 0)
      j = check(b,j);
   
   a[j]++;
   
   return 0;
   
}

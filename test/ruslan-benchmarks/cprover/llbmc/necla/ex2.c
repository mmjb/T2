#include "necla.h"
/* #include <stdlib.h> */
#define NULL 0

int * a;


inline int test(int * n ){

   int i;

   for (i = 0; i < (*n); ++i){

      a[i] = 0;
      
      
   }

   return 1;
}


int main(){

   int n = __NONDET__();
   ASSUME (n <= 100);
   
   if (n <= 0 || n >= 1024){
      exit(1);
   } else {
      a = (int *) malloc( n * sizeof(int));
   }

   ASSUME(a != NULL);

   test(&n);

   return 1;
}

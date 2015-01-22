#include "necla.h"
#include <stdlib.h>
#include <string.h>

typedef struct foo{
   
   int x;
   char * y;
   int z;

} foo_t;


foo_t * array;


int __llbmc_main(int n){
   int alen;  
   int * x;

   ASSUME( n > 0);
   ASSUME (n <= (1 << 20));

   array = (foo_t *) malloc(n * sizeof(foo_t));
   memset(array,0, sizeof(foo_t)* n);
   /*-- check
     Length(array) * sizeof(*array) >= sizeof(foo_t) * n
     
     --*/
   
   return 1;
}

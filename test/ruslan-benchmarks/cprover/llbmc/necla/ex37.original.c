#include "necla.h"
#include <stdlib.h>
typedef struct foo{
   
   int x;
   int z;

} foo_t;


int __llbmc_main(int n){
   foo_t * a;
   int * b;
   ASSUME(n > 0);
   ASSUME (n <= (1 << 20));
   
   a = (foo_t*) malloc(n * sizeof(foo_t));

   b = (int *) a; /*-- down casting. Length(b) = 2 * Length(a) --*/

   b[2*n -1 ] = '\0';
   

   return 1;
}

#include "necla.h"
extern int __NONDET__();

extern char x[100], y[100];
extern int i,j,k;

/* int __llbmc_main() {   */
int main() {  
  k = __NONDET__();
  
  i = 0;
  while(x[i] != 0){
    y[i] = x[i];
    i++;
  }
  y[i] = 0;
  
  if(k >= 0 && k < i)
    if(y[k] == 0)
      {
	return 1 ;
      }

  return 0 ;
}

/* 
   Benchmark ex40.c comment 
   (added in version 1.1, January 2011, by Franjo Ivancic, ivancic@nec-labs.com)

   Since the buffer x is external it may not contain a null-terminating character
   within the first 100 characters. This may then lead to overflows at the four 
   accesses to x and y near the while loop. Since the while loop may increase i 
   beyond 100, it is possible for the non-deterministic k to also be 100 or larger 
   thus causing an additional overflow. 
*/

#include "necla.h"

int a[100];

int main(){
   int hi=0, lo=99;

   while ( hi < lo){
      if (a[hi] < a[lo]){
         hi = (hi+lo)/2;
      } else {
         lo = (hi+lo)/2;
      }
   }

   return 0;
}

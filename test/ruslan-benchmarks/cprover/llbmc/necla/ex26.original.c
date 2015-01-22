#include "necla.h"

int foo(int x);
int a [100];
int b[200];

void g(int * x, int y){
   if (x == a)
      x[y]=0;
   else
      x[2*y] = 0;
}


int main(){
   int i,j;
   for(i=0; i < 100; ++i){
      g(a,i);
      g(b,i);
      foo(i);
   }

   for(j=100;j < 200; ++j){
      g(b,j);
      foo(j);
   }

   return 1;
   
}

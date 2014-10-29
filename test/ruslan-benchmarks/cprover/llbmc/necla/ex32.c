#include "necla.h"

struct foo{
   int x[1000];
};

inline int make_null(struct foo * hoo){
   int i;
   for (i=999; i >= 0; i--)
      hoo -> x[i]=0;
   return 0;

}

inline int no(int i){
   if (i == 0)
      make_null((struct foo*) 0);
   return 1;
}

int main(){
   struct foo hoo;
   no(1);
   make_null(&hoo);
   make_null(&hoo);

   return 1;
}

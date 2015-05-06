#include "necla.h"

int a[10];

inline int foo(int x){
    a[x]=1;
    return a[x];
}

int main(){
    int il;
    for(il=0; foo(il) && il  < 10; ++il){}

    for(il=0; il < 10 && foo(il) ; ++il){}

    return 1;
}

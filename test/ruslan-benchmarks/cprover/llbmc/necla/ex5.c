#include "necla.h"

int x,y;

int main(){
    int a[20];
    ASSUME(x >= 0);
    ASSUME(y >= 0);
    ASSUME(x< 9);
    ASSUME(y < 10);

    if (x * y - x*x >= 50){
        x=x+1;
    }

    a[x]=1;
    return 1;
}

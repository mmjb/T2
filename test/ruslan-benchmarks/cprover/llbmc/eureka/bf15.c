#include "llbmc.h"

int INFINITY = 899;
int main(){
  int nodecount = 5;
  int edgecount = 15;
  int source = 0;
  int Source[15] = {0,2,3,3,3,1,0,4,1,1,3,2,4,3,3};
  int Dest[15] = {1,2,3,4,2,1,0,2,4,0,1,4,1,1,2};
  int Weight[15] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14};
  int distance[5];
  int x,y;
  int i,j;

  for(i = 0; i < nodecount; i++){
    if(i == source){
      distance[i] = 0;
    }
    else {
      distance[i] = INFINITY;
    }
  }

  for(i = 0; i < nodecount; i++)
    {
      for(j = 0; j < edgecount; j++)
        {
          x = Dest[j];
          y = Source[j];
          if(distance[x] > distance[y] + Weight[j])
            {
              distance[x] = distance[y] + Weight[j];
            }
        }
    }
  for(i = 0; i < edgecount; i++)
    {
      x = Dest[i];
      y = Source[i];
      if(distance[x] > distance[y] + Weight[i])
        {
          return 0;
        }
    }

  for(i = 0; i < nodecount; i++)
    {
      __llbmc_assert(distance[i]>=0);
    }

  return 0;
}

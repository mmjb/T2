#include "slayer.h"

struct node {
  int data;
  int *next;
};

int main() {
  int *x = malloc(sizeof(int));
  free(x);
  return 0;
} 

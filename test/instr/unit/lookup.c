#include "slayer.h"

struct node {
  int data;
  int *next;
};

int main() {
  struct node *n = (struct node *) malloc(sizeof(struct node));
  int x = n->data;
  return 0;
} 

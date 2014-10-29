#include <stdlib.h>

typedef struct {
  int *status;
  char pero;
  int x;
  int *y;
} elem;

void setArray(elem *array) {
  *(array->status) = 20;
  array->x = 3;
}

int main() {
  elem *array = (elem*)malloc(sizeof(elem));
  array->status = (int*)malloc(sizeof(int));
  setArray(array);
  free(array->status);
  free(array);
  return 0;
}


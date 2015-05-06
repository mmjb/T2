#include <stdlib.h>

typedef struct {
  char pero;
  int *status;
  int *y;
  int x;
} elem;

void setArray(elem *array) {
  *(array[3].status) = 20;
  array[3].x = 3;
}

int main() {
  elem *array = (elem*)malloc(10 * sizeof(elem));
  array[3].status = (int*)malloc(sizeof(int));
  setArray(array);
  free(array);
  return 0;
}


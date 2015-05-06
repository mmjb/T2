#include <stdlib.h>

void setArray(int *array) {
  array[3] = 1;
}

void noop(int *array) {
  int x;
  x = array[3];
}

void setArrayOne(int *array) {
  noop(array);
  setArray(array);
  noop(array);
  setArray(array);
}

int main() {
  int *array = (int*)malloc(10 * sizeof(int));
  setArrayOne(array);
  free(array);
  return 0;
}


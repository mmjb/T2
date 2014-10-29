#include <stdlib.h>

void setArray(int *array) {
  array[3] = 1;
}

int main() {
  int *array = (int*)malloc(10 * sizeof(int));
  setArray(array);
  free(array);
  return 0;
}


#include <stdlib.h>
#include "smack.h"

typedef struct {
  char pero;
  int *status;
  int *y;
  int x;
} elem;

void setArray(elem *array) {
  int i;

  for (i = 0; i < 10; i++) {
    array[i].x = 33;
    array[i].status = NULL;
  }
}

void noop(elem *array) {
  int x;
  x = array[3].x;
}

void setArrayOne(elem *array) {
  noop(array);
  setArray(array);
  noop(array);
  setArray(array);
}

int main() {
  elem *array = (elem*)malloc(10 * sizeof(elem));
  setArrayOne(array);
  free(array);
  return 0;
}


/* #include <stdlib.h> */
#include "smack.h"

typedef struct {
  char pero;
  int *status;
  int *y;
  int x;
} elem;

inline void setArray(elem *array) {
  int i;

  for (i = 0; i < 10; i++) {
    array[i].x = 33;
    array[i].status = NULL;
  }
}

int main() {
  elem *array = (elem*)malloc(10 * sizeof(elem));
  setArray(array);
  free(array);
  return 0;
}


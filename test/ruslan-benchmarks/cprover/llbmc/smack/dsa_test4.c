/* #include <stdlib.h> */

typedef struct {
  char pero;
  int *status;
  int *y;
  int x;
} elem;

inline void setArray(elem *array) {
  array[3].x = 33;
  array[3].status = NULL;
  array[5].x = 55;
  array[5].status = NULL;
  array[8].x = 88;
  array[8].status = NULL;
}

int main() {
  elem *array = (elem*)malloc(10 * sizeof(elem));
  setArray(array);
  free(array);
  return 0;
}


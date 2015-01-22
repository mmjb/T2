#include <stdlib.h>
#include "smack.h"

typedef struct {
  int a;
  int b;
  int c;
  int d;
} elem;

typedef struct {
  int w;
  int x;
  int y;
  int z;
} elem1;

void setArray(void *arg) {
  int i;
  elem* array = (elem*) arg;

  for (i = 0; i < 10; i++) {
    array[i].a = 33;
    array[i].b = 32;
  }
}

void setArray1(void *arg) {
  int i;
  elem1* array = (elem1*) arg;

  for (i = 0; i < 10; i++) {
    array[i].x = 33;
    array[i].z = 34;
  }
}

int main() {
  elem *array = (elem*)malloc(10 * sizeof(elem));
  setArray(array);
  setArray1(array);
  free(array);
  return 0;
}


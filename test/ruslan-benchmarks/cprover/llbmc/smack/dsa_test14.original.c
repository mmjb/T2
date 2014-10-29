#include <stdlib.h>

int x;

void setArray(int *a) {
  *a = 1;
}

void setArrays() {
  setArray(&x);
}

int main() {
  setArrays();
  return 0;
}


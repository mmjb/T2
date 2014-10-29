#include <stdlib.h>

int x;

void setArray() {
  x = 1;
}

void setArrays() {
  setArray();
}

int main() {
  setArrays();
  return 0;
}


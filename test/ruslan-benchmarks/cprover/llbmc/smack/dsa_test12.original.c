#include <stdlib.h>

void setArray(const char *x) {
  char a;
  a = x[0];
}

void setArrays() {
  setArray("aa");
  setArray("bb");
}

int main() {
  setArrays();
  return 0;
}


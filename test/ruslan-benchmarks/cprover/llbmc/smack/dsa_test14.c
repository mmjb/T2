/* #include <stdlib.h> */

int x;

inline void setArray(int *a) {
  *a = 1;
}

inline void setArrays() {
  setArray(&x);
}

int main() {
  setArrays();
  return 0;
}


/* #include <stdlib.h> */

int x;

inline void setArray() {
  x = 1;
}

inline void setArrays() {
  setArray();
}

int main() {
  setArrays();
  return 0;
}


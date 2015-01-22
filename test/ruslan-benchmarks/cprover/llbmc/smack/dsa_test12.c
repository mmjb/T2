/* #include <stdlib.h> */

inline void setArray(const char *x) {
  char a;
  a = x[0];
}

inline void setArrays() {
  setArray("aa");
  setArray("bb");
}

int main() {
  setArrays();
  return 0;
}


/* #include <stdlib.h> */

inline void setArray(int *array) {
  array[3] = 1;
}

inline void setArrays(int *arr1, int *arr2) {
  setArray(arr1);
  setArray(arr2);
}

int main() {
  int *array = (int*)malloc(10 * sizeof(int));
  int *array1 = (int*)malloc(20 * sizeof(int));
  setArrays(array, array1);
  free(array);
  free(array1);
  return 0;
}


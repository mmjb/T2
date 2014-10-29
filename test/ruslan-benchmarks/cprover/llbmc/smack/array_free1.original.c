#include <stdlib.h>
#include "smack.h"

#define MAXSIZE 42

typedef struct _DATA DATA, *PDATA;

struct _DATA {
  int *f;
  int x;
};

DATA a[MAXSIZE];

void free_array() {
  int i;

  for (i = 0; i < MAXSIZE; i++) {
    if (a[i].f != 0) {
      free(a[i].f);
      a[i].f = 0;
    }
  }
}

int main() {
  free_array();
  return 0;
}


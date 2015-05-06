/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Create, traverse and keep deleting
**/

#include "slayer.h"

typedef struct _SLL_ENTRY {
  int Data;
  struct _SLL_ENTRY *Flink;
} SLL_ENTRY, *PSLL_ENTRY;

PSLL_ENTRY SLL_create(int length) {
  void* null = NULL;
  int i;
  PSLL_ENTRY head, tmp;

  head = null;
  for(i = 0; i < length; i++) {
    tmp = (PSLL_ENTRY)malloc(sizeof(SLL_ENTRY));
    tmp->Flink = head;
    head = tmp;
  }

  return head;
}

void traverse(PSLL_ENTRY head) {
  void* null = NULL;
  while(head != null) {
    head = head->Flink ;
  }
}

void SLL_destroy_seg(PSLL_ENTRY x, PSLL_ENTRY y) {
  PSLL_ENTRY t;

  while(x != y) {
    t = x;
    if (nondet()) { /*bug*/
      x = x->Flink;
      free(t);
    }
  }
}

void SLL_destroy(PSLL_ENTRY x) {
  void* null = NULL;
  SLL_destroy_seg(x, null);
}

void main(void) {
  PSLL_ENTRY head;

  head = SLL_create(nondet());
  traverse(head);
  SLL_destroy(head);
}

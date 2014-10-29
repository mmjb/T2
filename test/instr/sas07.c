/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Create and destroy a singly-linked list.

  Example from SAS'07: Arithmetic Strengthening for Shape Analysis
**/

#include "slayer.h"

typedef struct _SLL_ENTRY {
  int Data;
  struct _SLL_ENTRY *Flink;
} SLL_ENTRY, *PSLL_ENTRY;

void SLL_destroy_seg(PSLL_ENTRY x, PSLL_ENTRY y) {
  PSLL_ENTRY t;

  while(x != y) {
    t = x;
    x = x->Flink;
    free(t);
  }
}

void SLL_destroy(PSLL_ENTRY x) {
  void* null = NULL;
  SLL_destroy_seg(x, null);
}

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

void main() {
  int *i; int j;
  PSLL_ENTRY head, tmp;
  int length = nondet();

  head = NULL;
  i = (int *)malloc(sizeof(int));
  for(*i = 0; *i < length; (*i)++) {
    tmp = (PSLL_ENTRY)malloc(sizeof(SLL_ENTRY));
    tmp->Flink = head;
    head = tmp;
  }
  free(i);

#if 0
  SLL_destroy(head);
#else
  j = 0;
  while (j < length) {
    tmp = head;
    head = head->Flink;
    free(tmp);
    j++;
  }
#endif
}

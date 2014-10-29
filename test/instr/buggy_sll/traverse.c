/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Create and enter an infinite traversal
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
    if (nondet()) { /*bug*/
      head = head->Flink ;
    }
  }
}

void main(void) {
  PSLL_ENTRY head;

  head = SLL_create(nondet());
  traverse(head);
}

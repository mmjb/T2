#include "sll.h"

void main(void) {
  void* null = NULL;
	PSLL_ENTRY head, x;

	head = SLL_create(nondet());
	x = head;

	while (x != null) {
		x = x->Flink;
	}

	SLL_destroy(head);
}

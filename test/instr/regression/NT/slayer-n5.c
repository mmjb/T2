#include "sll.h"

void main(void) {
  void* null = NULL;
	PSLL_ENTRY head, x;
	int i;

	head = SLL_create(nondet());
	x = head;

	while (x != null) {
		i = nondet();

		while (i > 0 && x != null) {
			x = x->Flink;
			i--;
		}
	}

	SLL_destroy(head);
}

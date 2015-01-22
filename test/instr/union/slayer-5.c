#include "sll.h"

void main(void) {
  void* null = NULL;
	PSLL_ENTRY head, x;
	int i;

	head = SLL_create(nondet());
	x = head;

	while (x != null) {
		i = nondet();
		assume(i > 0);

		while (i > 0 && x != null) {
			x = x->Flink;
			i--;
		}
	}

	SLL_destroy(head);
}

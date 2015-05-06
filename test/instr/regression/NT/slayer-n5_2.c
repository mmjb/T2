#include "sll.h"

void main(void) {
	PSLL_ENTRY head, x;
	int i;

	head = SLL_create(nondet());
	x = head;

	while (x != NULL) {
		i = nondet();

		while (i > 0 && x != NULL) {
			x = x->Flink;
			i--;
		}
	}

	SLL_destroy(head);
}

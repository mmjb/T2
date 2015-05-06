#include "sll.h"

void main(void) {
	PSLL_ENTRY head, x;
	int i;

	head = SLL_create(nondet());
	x = head;

	while (x != NULL && i > 0) {
		if (nondet()) {
			i--;
		} else {
			x = x->Flink;
		}
	}

	SLL_destroy(head);
}

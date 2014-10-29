#include "sll.h"

void main(void) {
	PSLL_ENTRY head, x;

	head = SLL_create(nondet());
	x = head;

	while (x != NULL) {
		x = head->Flink;
	}

	SLL_destroy(head);
}

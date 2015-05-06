#include "sll.h"

void main(void) {
  void* null = NULL;
	PSLL_ENTRY head, x;
	int i;

	head = SLL_create(nondet());
	x = head;
	i = nondet();

	while (x != null && i > 0) {
		if (nondet()) {
			i++;
			SLL_destroy(head);
			head = SLL_create(nondet());
			x = head;
		} else {
			i = nondet();
			x = x->Flink;
		}
	}

	SLL_destroy(head);
}

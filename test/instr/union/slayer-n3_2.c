#include "sll.h"

void main(void) {
	PSLL_ENTRY head;
	int i;

	head = SLL_create(nondet());
	i = 100;

	while (head != NULL && i > 0) {
		if (nondet()) {
			i++;
		} else {
			head = head->Flink;
		}
	}
}

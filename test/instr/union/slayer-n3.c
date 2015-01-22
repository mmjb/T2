#include "sll.h"

void main(void) {
  void* null = NULL;
	PSLL_ENTRY head;
	int i;

	head = SLL_create(nondet());
	i = 100;

	while (head != null && i > 0) {
		if (nondet()) {
			i++;
		} else {
			head = head->Flink;
		}
	}
}

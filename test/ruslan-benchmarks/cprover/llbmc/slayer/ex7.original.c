#include <llbmc.h>
/* #include <stdlib.h> */

typedef struct _SLL_ENTRY
{
    int Data;
    struct _SLL_ENTRY *Flink;
} SLL_ENTRY, *PSLL_ENTRY;

PSLL_ENTRY SLL_create(int length)
{
    int i;
    PSLL_ENTRY head, tmp;
    head = NULL;
    for(i = 0; i < length; i++) {
        tmp = (PSLL_ENTRY)malloc(sizeof(SLL_ENTRY));
        tmp->Flink = head;
        head = tmp;
    }
    return head;
}

int main(void)
{
    PSLL_ENTRY head;

    int s = __llbmc_nondef_int();
    __llbmc_assume(s <= 10);
    head = SLL_create(10);

    return 0;
}

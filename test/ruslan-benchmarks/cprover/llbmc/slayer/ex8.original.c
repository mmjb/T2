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

void SLL_destroy_seg(PSLL_ENTRY x, PSLL_ENTRY y)
{
    PSLL_ENTRY t;
    while(x != y) {
        t = x;
        x = x->Flink;
        free(t);
    }
}

void SLL_destroy(PSLL_ENTRY x)
{
    SLL_destroy_seg(x, NULL);
}

/*
 *   Reverse the list pointed to by l.
 *   Implemented by poping off each item of *l into r.
 * */
void reverse(PSLL_ENTRY *l)
{
    PSLL_ENTRY c = *l, r = NULL;
    while(c != NULL) {
        PSLL_ENTRY t;
        t = c;
        c = c->Flink;
        t->Flink = r;
        r = t;
    }
    *l = r;
}

int main()
{
    PSLL_ENTRY head;
    int s = __llbmc_nondef_int();
    __llbmc_assume(s <= 5);
    head = SLL_create(s);
    reverse(&head);
    SLL_destroy(head);
    return 0;
}

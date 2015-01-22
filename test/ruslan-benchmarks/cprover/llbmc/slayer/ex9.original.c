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

PSLL_ENTRY copy(PSLL_ENTRY a)
{
    PSLL_ENTRY y, x = a;
    SLL_ENTRY* * z = &y;

    while(x != NULL) /* listseg(y,*z) * listseg(-,x) * list(x) */ {
        *z = (SLL_ENTRY*)malloc(sizeof(SLL_ENTRY));
        (*z)->Data = x->Data;
        z = &(*z)->Flink;
        x = x->Flink;
    }
    *z = NULL;
    return y;
}

int main()
{
    PSLL_ENTRY x = NULL, y = NULL;
    int s = __llbmc_nondef_int();
    __llbmc_assume(s <= 5);
    x = SLL_create(s);
    y = copy(x);
    SLL_destroy(x);
    SLL_destroy(y);
    return 0;
}

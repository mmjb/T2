void main()
{

    int x;
    int *a = &x;
    int *b = a;
    int *c = b;
    int *d = c;
    int *e = d;
    int *f = e;
    int *g = f;
    int *h = g;
    while(1) {

        if ((*a)<0) {
            (*b) = -1 * (*c);
            (*d)--;
        } else if ((*e)>0) {
            (*f) = -1 * (*g);
            (*h)++;
        } else {
            return;
        }

        if ((*a)<0) {
            (*b) = -1 * (*c);
            (*d)--;
        } else if ((*e)>0) {
            (*f) = -1 * (*g);
            (*h)++;
        } else {
            return;
        }


    }
}

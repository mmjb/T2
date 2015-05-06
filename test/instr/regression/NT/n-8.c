void main()
{
    int x;
    int y;
    int * p = &x;

    while(x<y) {
        if (nondet()) {
            (*p)++;
        }
    }
}

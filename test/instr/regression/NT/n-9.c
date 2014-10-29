void main()
{
    int x;
    int y;
    int * p = &x;

    while((*p)<y) {
        if (nondet()) {
            x++;
        }
    }
}

int foo(int * p)
{
    if ((*p)>0) {
        (*p)++;
        return 1;
    }
    return 0;
}


void main()
{
    int x;

    while(foo(&x)) {}
}

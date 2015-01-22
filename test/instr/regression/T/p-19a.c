void main()
{
    int x;
    int * p = &x;
    int ** q = &p;

    while((**q)>0) {
       (**q)--;
    }
}

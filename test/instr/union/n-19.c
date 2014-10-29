void main()
{
    int x;
    int * p = &x;
    int ** q;

    if (nondet()) { q = &p;}

    while((**q)>0) {
       x--;
    }
}

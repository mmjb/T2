void main()
{
    int x;

    X: if (x<0)
           goto E;
       if (nondet()) x--;
       goto X;
    E:0;
}

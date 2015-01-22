void main()
{
    int x;

    X: if (x<0) goto E;
       goto I;
       goto X;
    E: goto F;

    I: x--;
    F: 0;
}

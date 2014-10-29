void main()
{
    int x;

    for(;;) {
       x--;
       if (x==13) x = nondet();
       if (x<0) break;
    }
}

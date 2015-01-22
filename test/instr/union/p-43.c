void main()
{
    int x,y;

    while (x>0 && y>0 && x+y>0 ) {
        if (nondet()) {
            x--;
            y=x;
        } else {
            x =y-2;
            y=x+1;
        }
    }
}

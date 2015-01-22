void main()
{
    int x;
    int y;
    int b=0;

    while(x<y) {
        if (b<=0) {
            b=1;
            x++;
        } else {
            b=0;
            y--;
        }
    }
}

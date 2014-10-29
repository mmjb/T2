void main()
{
    int x;

    while(1) {

        if (x<0) {
            x = -1 * x;
            x-=2;
        } else if (x>0) {
            x = -1 * x;
            x+=2;
        } else {
            return;
        }
    }
}

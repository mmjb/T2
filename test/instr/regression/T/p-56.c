void main()
{
    int x,y;
    int k;
    int w;

    if (k>0 && w>0) {

        while (x<0) {
            x++;
            y++;
            if (y==0) {
                y=k;
                if (k>0) { k--; }
                x=x-w;
            }
        }
    }
}

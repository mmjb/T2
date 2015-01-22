void main()
{

    int y;
    int * py = &y;

    int x;
    int * px = &x;

    int ** q = &px;

    while((**q)>0) {
       x--;
       q = &py;
    }
}

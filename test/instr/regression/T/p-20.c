void main()
{

    int y;
    int * py = &y;

    int x;
    int * px = &x;

    int ** q = &py;

    while((**q)>0) {
       x--;
       q = &px;
    }
}


void main()
{
    int x;
    int y;

    while(x<y) {
        if (nondet()) x++;
        else y--;
    }
}

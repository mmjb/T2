// Currently fails, problem seems to be that x,y are globals
int x;
int y;

void main()
{
    while(x<y) {
        x++;
    }
}

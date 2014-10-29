// Currently fails, problem seems to be that x,y are globals
int x;
int y;

void main()
{
    x = nondet();
    y = nondet();

    while(x<y) {
        x++;
    }
}

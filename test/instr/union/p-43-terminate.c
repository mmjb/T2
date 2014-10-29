void main()
{
    int x,y;
    int ox, oy, c;
    int err = 0;

    c = 0;

    while (x>0 && y>0 && x+y>0 ) {
	if (c == 0 && nondet()) {
	    c = 1;
    	    ox = x;
    	    oy = y;
	} else if (c == 1) {
		if (x >= ox && y >= oy && (x + y) >= (ox + oy)) {
			err = 1;
		}
	}

        if (nondet()) {
            x--;
            y=x;
        } else {
            x =y-2;
            y=x+1;
        }
    }
}

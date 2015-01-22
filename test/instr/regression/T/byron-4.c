int main(void) {
	int x;
	int b;

	assume(x>0);
	b = 1;


	while (x!=0) {
		if (b == 1) {
			x--;
			b = 0;
		} else {
		        x++;
			b = 1;
		}

		x = x * -1;
	}
}

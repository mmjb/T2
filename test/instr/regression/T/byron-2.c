int main(void) {
	int x;
	int y;

	while (x > 0) {
		if (nondet()) {
			x--;
			y = nondet();
		} else {
			y--;
			assume(y > 0);
		}
	}
}


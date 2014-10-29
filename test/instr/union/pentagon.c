int main(void) {
	int a, b, c, d, e;

	a = nondet();
	b = nondet();
	c = nondet();
	d = nondet();
	e = nondet();

	while (a < 0 || b < 0 || c < d || e < 0) {
		if (a < 0) {
			a = -a;
			b -= a;
			e -= a;
		} else if (b < 0) {
			b = -b;
			a -= b;
			c -= b;
		} else if (c < 0) {
			c = -c;
			b -= c;
			d -= c;
		} else if (d < 0) {
			d = -d;
			c -= d;
			e -= d;
		} else if (e < 0) {
			e = -e;
			d -= e;
			a -= e;
		}
	}
}

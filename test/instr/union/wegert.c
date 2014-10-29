void main() {
	int a,b,c,d,e;

	while (a+b+c+d+e>1) {
		if (nondet() && a<0) {
			e = e + a;
			b = b + a;
			a = a * -1;
		} else if (nondet() && b<0) {
			a = a + b;
			c = c + b;
			b = b * -1;
		} else if (nondet() && c<0) {
			b = b + c;
			d = d + c;
			c = c * -1;
		} else if (nondet() && d<0) {
			c = c + d;
			e = e + d;
			d = d * -1;
		} else if (nondet() && e<0) {
			d = d + e;
			e = a + e;
			e = e * -1;
        } else {
			break;
		}
	}
}


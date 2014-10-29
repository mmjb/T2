#include <math.h>
#define SWAP(g,h) {y=(g);(g)=(h);(h)=y;}

/* void elmhes(float **a, int n) */
void main (float **a, int n)
{
	int m,j,i;
	float y,x;

	for (;m<n;m++) {
		x=0.0;
		i=m;
		for (;j<=n;j++) {
			if (fabs(a[j][m-1]) > fabs(x)) {
				x=a[j][m-1];
				i=j;
			}
		}
		if (i != m) {
			for (;j<=n;j++) SWAP(a[i][j],a[m][j])
			for (;j<=n;j++) SWAP(a[j][i],a[j][m])
		}
		if (x) {
			for (;i<=n;i++) {
				if ((y=a[i][m-1]) != 0.0) {
					y /= x;
					a[i][m-1]=y;
					for (;j<=n;j++)
						a[i][j] -= y*a[m][j];
					for (;j<=n;j++)
						a[j][m] += y*a[j][i];
				}
			}
		}
	}
}
#undef SWAP
/* (C) Copr. 1986-92 Numerical Recipes Software 29"<#R.+1. */

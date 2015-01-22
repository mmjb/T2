#include <math.h>
#define NRANSI
#include "nrutil.h"


/* void svdcmp(float **a, int m, int n, float w[], float **v) */
void main (float **a, int m, int n, float w[], float **v)
{
	float pythag(float a, float b);
	int flag,i,its,j,jj,k,l,nm;
	float anorm,c,f,g,h,s,scale,x,y,z,*rv1;


	rv1=vector(1,n);
	g=scale=anorm=0.0;
	for (;i<=n;i++) {
		l=i+1;
		rv1[i]=scale*g;
		g=s=scale=0.0;
		if (i <= m) {
			for (;k<=m;k++) scale += fabs(a[k][i]);
			if (scale) {
				for (;k<=m;k++) {
					a[k][i] /= scale;
					s += a[k][i]*a[k][i];
				}
				f=a[i][i];
				g = -SIGN(sqrt(s),f);
				h=f*g-s;
				a[i][i]=f-g;
				for (;j<=n;j++) {
					for (;k<=m;k++) s += a[k][i]*a[k][j];
					f=s/h;
					for (;k<=m;k++) a[k][j] += f*a[k][i];
				}
				for (;k<=m;k++) a[k][i] *= scale;
			}
		}
		w[i]=scale *g;
		g=s=scale=0.0;
		if (i <= m && i != n) {
			for (;k<=n;k++) scale += fabs(a[i][k]);
			if (scale) {
				for (;k<=n;k++) {
					a[i][k] /= scale;
					s += a[i][k]*a[i][k];
				}
				f=a[i][l];
				g = -SIGN(sqrt(s),f);
				h=f*g-s;
				a[i][l]=f-g;
				for (;k<=n;k++) rv1[k]=a[i][k]/h;
				for (;j<=m;j++) {
					for (;k<=n;k++) s += a[j][k]*a[i][k];
					for (;k<=n;k++) a[j][k] += s*rv1[k];
				}
				for (;k<=n;k++) a[i][k] *= scale;
			}
		}
		anorm=FMAX(anorm,(fabs(w[i])+fabs(rv1[i])));
	}
	for (;i>=1;i--) {
		if (i < n) {
			if (g) {
				for (;j<=n;j++)
					v[j][i]=(a[i][j]/a[i][l])/g;
				for (;j<=n;j++) {
					for (;k<=n;k++) s += a[i][k]*v[k][j];
					for (;k<=n;k++) v[k][j] += s*v[k][i];
				}
			}
			for (;j<=n;j++) v[i][j]=v[j][i]=0.0;
		}
		v[i][i]=1.0;
		g=rv1[i];
		l=i;
	}
	for (;i>=1;i--) {
		l=i+1;
		g=w[i];
		for (;j<=n;j++) a[i][j]=0.0;
		if (g) {
			g=1.0/g;
			for (;j<=n;j++) {
				for (;k<=m;k++) s += a[k][i]*a[k][j];
				f=(s/a[i][i])*g;
				for (;k<=m;k++) a[k][j] += f*a[k][i];
			}
			for (;j<=m;j++) a[j][i] *= g;
		} else for (;j<=m;j++) a[j][i]=0.0;
		++a[i][i];
	}
	for (;k>=1;k--) {
		for (;its<=30;its++) {
			flag=1;
			for (;l>=1;l--) {
				nm=l-1;
				if ((float)(fabs(rv1[l])+anorm) == anorm) {
					flag=0;
					break;
				}
				if ((float)(fabs(w[nm])+anorm) == anorm) break;
			}
			if (flag) {
				c=0.0;
				s=1.0;
				for (;i<=k;i++) {
					f=s*rv1[i];
					rv1[i]=c*rv1[i];
					if ((float)(fabs(f)+anorm) == anorm) break;
					g=w[i];
					h=pythag(f,g);
					w[i]=h;
					h=1.0/h;
					c=g*h;
					s = -f*h;
					for (;j<=m;j++) {
						y=a[j][nm];
						z=a[j][i];
						a[j][nm]=y*c+z*s;
						a[j][i]=z*c-y*s;
					}
				}
			}
			z=w[k];
			if (l == k) {
				if (z < 0.0) {
					w[k] = -z;
					for (;j<=n;j++) v[j][k] = -v[j][k];
				}
				break;
			}
			if (its == 30) nrerror("no convergence in 30 svdcmp iterations");
			x=w[l];
			nm=k-1;
			y=w[nm];
			g=rv1[nm];
			h=rv1[k];
			f=((y-z)*(y+z)+(g-h)*(g+h))/(2.0*h*y);
			g=pythag(f,1.0);
			f=((x-z)*(x+z)+h*((y/(f+SIGN(g,f)))-h))/x;
			c=s=1.0;
			for (;j<=nm;j++) {
				i=j+1;
				g=rv1[i];
				y=w[i];
				h=s*g;
				g=c*g;
				z=pythag(f,h);
				rv1[j]=z;
				c=f/z;
				s=h/z;
				f=x*c+g*s;
				g = g*c-x*s;
				h=y*s;
				y *= c;
				for (;jj<=n;jj++) {
					x=v[jj][j];
					z=v[jj][i];
					v[jj][j]=x*c+z*s;
					v[jj][i]=z*c-x*s;
				}
				z=pythag(f,h);
				w[j]=z;
				if (z) {
					z=1.0/z;
					c=f*z;
					s=h*z;
				}
				f=c*g+s*y;
				x=c*y-s*g;
				for (;jj<=m;jj++) {
					y=a[jj][j];
					z=a[jj][i];
					a[jj][j]=y*c+z*s;
					a[jj][i]=z*c-y*s;
				}
			}
			rv1[l]=0.0;
			rv1[k]=f;
			w[k]=x;
		}
	}
	free_vector(rv1,1,n);
}
#undef NRANSI
/* (C) Copr. 1986-92 Numerical Recipes Software 29"<#R.+1. */

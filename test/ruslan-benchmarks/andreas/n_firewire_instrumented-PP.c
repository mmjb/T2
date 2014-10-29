



void main() {

  int xx, yy;
  int NONDET;

  int z; int pos; z = NONDET; assume (z >= 0); pos = 0; int next = 1;

  int N = NONDET;
  assume (N >= 1);

  int K = N;

  xx = 0;
  yy = 0;

  while (K > 0) {


    xx = NONDET;
    assume (xx >= 0);
    assume (xx <= 1);

    if (z <= 0) {
      if (pos <= 0) { assume (xx <= 0); pos++; }
      else if (pos <= 1) { assume (xx >= 1); pos++;}
      else if (pos <= 2) { assume (xx <= 0); pos++;}
    else { next++; z = NONDET; assume (z >= 0); pos = 0; } } else {z--;}


    yy = NONDET;
    assume (yy >= 0);
    assume (yy <= 1);

    if (z <= 0) {
      if (pos <= 0) { assume (yy <= 0); pos++; }
      else if (pos <= 1) { assume (yy >= 1); pos++;}
      else if (pos <= 2) { assume (yy <= 0); pos++;}
    else { next++; z = NONDET; assume (z >= 0); pos = 0; } } else {z--;}

    if (xx != yy) K--;

  }
}

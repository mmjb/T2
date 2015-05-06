#include "necla.h"
/*
  fn1 returns a positive value less than n.
*/
int fn1(int n) {
    int ret = __NONDET__();
    ASSUME(0 <= ret);
    ASSUME(ret < n);
    return ret;
}

int main() {
    int i1 = fn1(2); /* 0 or 1 */
    int i2 = fn1(2); /* 0 or 1 */
    int i3 = fn1(2); /* 0 or 1 */
    int i4 = fn1(2); /* 0 or 1 */
    int i5 = fn1(2); /* 0 or 1 */
    int i6 = fn1(2); /* 0 or 1 */
    int i7 = fn1(2); /* 0 or 1 */
    int i8 = fn1(2); /* 0 or 1 */
    ASSERT(i1 + i2 + i3 + i4 + i5 + i6 + i7 + i8 <= 8); /* should be proved */
    return 0;
}

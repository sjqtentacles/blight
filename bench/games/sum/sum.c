#include <stdio.h>

/* sum of 1..1000 = 500500, matching the shared golden. */
int main(void) {
    long long acc = 0;
    for (int i = 1; i <= 1000; i++) {
        acc += i;
    }
    printf("%lld\n", acc);
    return 0;
}

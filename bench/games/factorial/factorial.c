#include <stdio.h>

/* 20! = 2432902008176640000 (fits in a signed 64-bit int), matching the shared golden. */
int main(void) {
    long long acc = 1;
    for (int i = 1; i <= 20; i++) {
        acc *= i;
    }
    printf("%lld\n", acc);
    return 0;
}

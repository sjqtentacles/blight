#include <stdio.h>

/* fib(30) via an iterative two-element window; output matches the shared golden. */
int main(void) {
    long long a = 0, b = 1;
    for (int i = 0; i < 30; i++) {
        long long next = a + b;
        a = b;
        b = next;
    }
    printf("%lld\n", a);
    return 0;
}

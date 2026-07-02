/* hofold.c — C reference for the higher-order fold benchmark (P10). Applies a step function to an
 * accumulator 10^6 times via a function pointer, mirroring Blight's indirect closure apply. Prints
 * 1000000. (-O2 may devirtualize/fold the loop — that is exactly the optimized lower bound.) */
#include <stdio.h>

static long add1(long a) { return a + 1; }

static long iterate(long fuel, long (*step)(long), long acc) {
    for (long i = 0; i < fuel; i++) acc = step(acc);
    return acc;
}

int main(void) {
    printf("%ld\n", iterate(1000000L, add1, 0L));
    return 0;
}

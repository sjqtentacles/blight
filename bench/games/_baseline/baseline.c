#include <stdio.h>

/* Near-empty program: starts the C runtime, prints the same single value the real benches print, and
 * exits. Its peak RSS is the language's startup/runtime floor, subtracted from each problem's peak RSS
 * to give a startup-adjusted "RSS delta" (the algorithmic memory) in bench/game.sh. */
int main(void) {
  printf("0\n");
  return 0;
}

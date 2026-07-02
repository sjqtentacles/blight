# listfold: build the list [1..N], map (*2) into a second list, then fold-sum it. Mirrors
# listfold_int.bl; the result is sum_{i=1..N} 2*i = N*(N+1) = 100010000 for N = 10000 (shared
# golden). Allocates two N-element lists to exercise a linear (list-shaped) allocation pattern.

xs = list(range(1, 10001))
ys = [x * 2 for x in xs]
print(sum(ys))

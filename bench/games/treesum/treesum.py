import sys

# treesum: build a full binary tree of depth 20 (each internal node labeled 1) and sum every node
# label. Mirrors treesum_int.bl; leaves contribute 0 so the sum is the internal-node count
# 2^20 - 1 = 1048575 (shared golden). Allocates ~2^21 tuple nodes to stress the allocator.

sys.setrecursionlimit(1 << 20)


def build(depth):
    if depth == 0:
        return None  # leaf
    return (build(depth - 1), 1, build(depth - 1))


def tree_sum(t):
    if t is None:
        return 0
    l, x, r = t
    return tree_sum(l) + x + tree_sum(r)


print(tree_sum(build(20)))

#include <stdio.h>
#include <stdlib.h>

/* treesum: build a full binary tree of depth 20 (each internal node labeled 1), then sum every
 * node label. Mirrors treesum_int.bl: leaves contribute 0, so the sum equals the internal-node
 * count = 2^20 - 1 = 1048575 (shared golden). Allocates/frees ~2^21 nodes to stress the allocator. */
typedef struct Node {
    struct Node *l;
    long long x;
    struct Node *r;
} Node;

static Node *build(int depth) {
    if (depth == 0) return NULL; /* leaf */
    Node *n = malloc(sizeof(Node));
    n->x = 1;
    n->l = build(depth - 1);
    n->r = build(depth - 1);
    return n;
}

static long long tree_sum(Node *t) {
    if (t == NULL) return 0;
    long long s = tree_sum(t->l) + t->x + tree_sum(t->r);
    return s;
}

static void freetree(Node *t) {
    if (t == NULL) return;
    freetree(t->l);
    freetree(t->r);
    free(t);
}

int main(void) {
    Node *t = build(20);
    printf("%lld\n", tree_sum(t));
    freetree(t);
    return 0;
}

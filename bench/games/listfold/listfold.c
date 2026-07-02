#include <stdio.h>
#include <stdlib.h>

/* listfold: build the linked list [1..N], map (*2) into a second list, then fold-sum it. Mirrors
 * listfold_int.bl; the result is sum_{i=1..N} 2*i = N*(N+1) = 100010000 for N = 10000 (shared
 * golden). Allocates ~2N cons nodes to exercise a linear (list-shaped) allocation pattern. */
typedef struct Node {
    long long x;
    struct Node *next;
} Node;

static Node *range(int n) { /* [1..n] */
    Node *head = NULL, *tail = NULL;
    for (int i = 1; i <= n; i++) {
        Node *nd = malloc(sizeof(Node));
        nd->x = i;
        nd->next = NULL;
        if (tail) tail->next = nd; else head = nd;
        tail = nd;
    }
    return head;
}

static Node *map_double(Node *xs) {
    Node *head = NULL, *tail = NULL;
    for (Node *p = xs; p; p = p->next) {
        Node *nd = malloc(sizeof(Node));
        nd->x = p->x * 2;
        nd->next = NULL;
        if (tail) tail->next = nd; else head = nd;
        tail = nd;
    }
    return head;
}

static long long fold_sum(Node *xs) {
    long long s = 0;
    for (Node *p = xs; p; p = p->next) s += p->x;
    return s;
}

int main(void) {
    Node *xs = range(10000);
    Node *ys = map_double(xs);
    printf("%lld\n", fold_sum(ys));
    return 0;
}

// treesum: build a full binary tree of depth 20 (each internal node labeled 1) and sum every node
// label. Mirrors treesum_int.bl; leaves contribute 0 so the sum is the internal-node count
// 2^20 - 1 = 1048575 (shared golden). Allocates ~2^21 boxed nodes to stress the allocator.

enum Tree {
    Leaf,
    Node(Box<Tree>, i64, Box<Tree>),
}

fn build(depth: u32) -> Tree {
    if depth == 0 {
        Tree::Leaf
    } else {
        Tree::Node(Box::new(build(depth - 1)), 1, Box::new(build(depth - 1)))
    }
}

fn tree_sum(t: &Tree) -> i64 {
    match t {
        Tree::Leaf => 0,
        Tree::Node(l, x, r) => tree_sum(l) + x + tree_sum(r),
    }
}

fn main() {
    let t = build(20);
    println!("{}", tree_sum(&t));
}

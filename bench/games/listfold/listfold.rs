// listfold: build the list [1..N], map (*2) into a second list, then fold-sum it. Mirrors
// listfold_int.bl; the result is sum_{i=1..N} 2*i = N*(N+1) = 100010000 for N = 10000 (shared
// golden). Allocates two N-element Vecs to exercise a linear (list-shaped) allocation pattern.

fn main() {
    let xs: Vec<i64> = (1..=10000).collect();
    let ys: Vec<i64> = xs.iter().map(|x| x * 2).collect();
    let s: i64 = ys.iter().sum();
    println!("{}", s);
}

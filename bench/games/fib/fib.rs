fn main() {
    let mut a: i64 = 0;
    let mut b: i64 = 1;
    for _ in 0..30 {
        let next = a + b;
        a = b;
        b = next;
    }
    println!("{a}");
}

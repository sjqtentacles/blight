fn main() {
    let mut acc: i64 = 1;
    for i in 1..=20 {
        acc *= i;
    }
    println!("{acc}");
}

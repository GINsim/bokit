use bokit::*;

fn main() {
    println!("A simple example!");

    let mut variables = VarSpace::default();
    let first = variables.provide("first").unwrap();
    let test = variables.provide("test").unwrap();
    let other = variables.provide("other").unwrap();
    let myvar = variables.provide("myvar").unwrap();

    let e: Expr = (test | other) & true & ((!myvar | first) & test);

    println!("Basic expression: {}", &e);
}

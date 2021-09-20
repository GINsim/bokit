use bokit::*;

fn main() {
    println!("A simple example!");

    let mut variables = VariableCollection::default();
    let first = variables.add("first").unwrap();
    let test = variables.add("test").unwrap();
    let other = variables.add("other").unwrap();
    let myvar = variables.add("myvar").unwrap();

    let e: Expr = (test | other) & true & ((!myvar | first) & test);

    println!("Basic expression: {}", &e);
}

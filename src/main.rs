use pluscal::prelude::*;

fn main() {
    let mut module = Module::new("tranfer");
    module.extends("Naturals");
    module.extends("TLC");

    let alice = module.natural("alice").value(10);
    let bob = module.natural("bob").value(10);
    let money = module.natural("money").in_range(1, 20);

    let transfer = module.label("Transfer");
    transfer
        .if_(alice.ge(&money))
        .then(|ctx| {
            let a = ctx.label("A");
            a.exec(alice.set(alice.minus(&money)));

            let b = ctx.label("B");
            b.exec(bob.set(bob.plus(&money)));
        })
        .end_if();

    println!("{}", module);
}

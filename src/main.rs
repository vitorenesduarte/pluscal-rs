use pluscal::prelude::*;

fn main() {
    /*
    ---- MODULE Transfer ----
    EXTENDS Naturals, TLC

    (* --algorithm transfer
    variables alice = 10,
              bob = 10,
              money \in 1..20;

    begin
    Transfer:
      if alice >= money then
        A: alice := alice - money;
        B: bob := bob + money;
    end if;
    C: assert alice >= 0;

    end algorithm *)
    ====
    */
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
            ctx.exec(alice.set(alice.minus(&money)));
            ctx.exec(bob.set(bob.plus(&money)));
        })
        .end_if();

    println!("{}", module);
}

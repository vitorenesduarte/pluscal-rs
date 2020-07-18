## pluscal-rs

Let's write some PlusCal in Rust! 

### The What

```rust
let mut module = Module::new("transfer");
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
```

The above Rust code outputs (example from the [Learn TLA+ website](https://learntla.com/introduction/example/)):

```pluscal
---- MODULE transfer ----
EXTENDS Naturals, TLC

(* --algorithm transfer

variables
    alice = 10,
    bob = 10,
    money \in 1..20;

begin

Transfer:
    if alice >= money then
        A:
            alice := alice - money;
        B:
            bob := bob + money;
    end if;

end algorithm *)
====
```

### The Why

I'm afraid I don't have a good answer. I can at least blame [this PLTalk](https://www.twitch.tv/videos/682775459) with Jean Yang, Hongyi Hu and Hillel Wayne on Practical Formal Methods.


## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.

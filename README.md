# tinka

Try it out at https://atennapel.github.io/tinka

```
TODO:
- primitive equality type
- primitive nat
- primitive fin
QUESTIONS:
- in surface syntax, seperate globals, vars and prims, or not?
- how to prevent unneeded eta-expansions
    Z : Nat
    Z : {-A : *} -> A -> (A -> A) -> A
    \{A}. Z {?0} : A -> (A -> A) -> A
    \{A}. Z {A}
```

# tinka

Try it out at https://atennapel.github.io/tinka

```
TODO:
- fix issues with mod and axiom k
- avoid shift/subst in import/sig/mod
QUESTIONS:
- in surface syntax, seperate globals, vars and prims, or not?
- how to prevent unneeded eta-expansions
    Z : Nat
    Z : {-A : *} -> A -> (A -> A) -> A
    \{A}. Z {?0} : A -> (A -> A) -> A
    \{A}. Z {A}
```

# tinka

Try it out at https://atennapel.github.io/tinka

```
// REPL
yarn start

// typecheck file
yarn start example.p
```

```
todo:
- fix stack overflow in nat elimination
- glue sigma named projection better
- translate more to primitives (PropEq, Refl, Fin)
- add primitive eliminators (NatS, FinS)
- local glued values
- fix linear let values
- metas
- elaboration with metas
- remove implicit arguments from primitive constructs
- fix importing in web repl
- rewrite parser, include locations
- improve elaboration of import
- de-elaborate annotations
```

```
questions:
- is eta-law for sigmas consistent for linear/erased sigmas?
- should I add eta law for equality?
```

# tinka

Try it out at https://atennapel.github.io/tinka

```
todo:
- add more identities for nat:
  - eq (add x n) 0 = false (for n > 0)
  - sub (add x n) m = add x (sub n m) (?)
- add native Fin
- does indVoid need elimination?
- combine all prim eliminators
- add functions for vec (head, tail, index, S-is-cons)
- maybe eqElim should not be erased?
- fix annotated let parser
- fix parsing empty file
- allow standalone projection
- create a CEK machine
- reset metas before
- insert skolems in check
- zonk all elims
- figure out glued vars
- add some better way to pretty print values for repl
- add pretty print for lists of nats
- find some way to automatically fill named holes (instance search)
```

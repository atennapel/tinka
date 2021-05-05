# tinka

A dependently typed programming language with a very small core language.
Try it out at https://atennapel.github.io/tinka

FEATURES:
- Type-in-type, not consistent, but type-safe
- Erasure annotations
- Implicit parameters with type inference

TODO:
- [x] add general indexed fixpoint type
- [x] update libs to use fixpoint
- [x] add heterogenous equality type with axiom K
- [ ] add codata fixpoint type
- [x] fix importing in web repl
- [ ] add testing
- [ ] fix negative vars in output
- [x] typed metas
- [x] make sure metas solutions are correct with respect to erasure
- [ ] have smarter way to verify meta solutions
- [ ] pruning and intersecting
- [ ] fix case-insensitive filesystem support
- [x] add primitive Nat
- [x] add primitive Fin
- [ ] replace void, unit, bool with Fin
- [ ] add surface syntax for modules
- [ ] bootstrap descriptions
- [ ] indexed descriptions
- [ ] check applications in elaboration

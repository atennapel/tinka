# tinka

A dependently typed programming language with a very small core language.
Try it out at https://atennapel.github.io/tinka

FEATURES:
- Type-in-type, not consistent, but type-safe
- Inductive-recursive datatypes using a functor fixpoint
- Erasure annotations
- Implicit parameters with type inference

TODO:
- [x] add general indexed fixpoint type
- [x] update libs to use fixpoint
- [x] add heterogenous equality type with axiom K
- [x] research inductive-recursive fixpoints
- [x] implement inductive-recursive fixpoints
- [x] test inductive-recursive fixpoints
- [x] separate file/url references in syntax
- [x] multi-line comments
- [x] fix importing in web repl
- [x] typed metas
- [x] make sure metas solutions are correct with respect to erasure
- [x] add primitive Nat
- [x] add primitive Fin
- [x] pruning and intersecting
- [ ] add delayed unification in elaboration
- [ ] check applications in elaboration
- [ ] fix negative vars in output
- [ ] have smarter way to verify meta solutions
- [ ] add syntax to explicitly reference local (debruijn)
- [ ] add codata fixpoint type
- [ ] add symbols and enumerations
- [ ] add testing
- [ ] fix case-insensitive filesystem support
- [ ] replace void, unit, bool with Fin
- [ ] add surface syntax for modules
- [ ] add surface syntax for datatypes
- [ ] inductive-inductive fixpoints

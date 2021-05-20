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
- [ ] test inductive-recursive fixpoints
- [x] separate file/url references in syntax
- [ ] add delayed unification in elaboration
- [ ] add codata fixpoint type
- [ ] add symbols and enumerations
- [x] fix importing in web repl
- [ ] add syntax to explicitly reference local (debruijn), global and primitive vars
- [ ] add testing
- [ ] fix negative vars in output
- [x] typed metas
- [x] make sure metas solutions are correct with respect to erasure
- [ ] pruning and intersecting
- [ ] have smarter way to verify meta solutions
- [ ] fix case-insensitive filesystem support
- [x] add primitive Nat
- [x] add primitive Fin
- [ ] replace void, unit, bool with Fin
- [ ] add surface syntax for modules
- [ ] check applications in elaboration
- [ ] inductive-inductive fixpoints

let Nat = {0 A : Type} -> A -> (A -> A) -> A;
let Z : Nat = \{A} z s. z;
let S : Nat -> Nat = \n {A} z s. s (n {A} z s);

let UnitType = {0 A : Type} -> A -> A;
let Unit : UnitType = \{A} x. x;

(Nat, Z, S, *) : (0 Nat : Type) ** (Z : Nat) ** (S : Nat -> Nat) ** ()

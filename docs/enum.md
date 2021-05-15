Enumerations, to help with defining labeled constructors for datatypes.
```
---------------------
{| l_1 ... l_n |} : *

l is in { l_1 ... l_n }
----------------------
'l : {| l_1 ... l_n |}

t_i : A
----------------------------------------------------------
{| l_1 => t_1; ...; l_n => t_n |} : {| l_1 ... l_n |} -> A

P : {| l_1 ... l_n |} -> *
t_i : P 'l_i
----------------------------------------------------------------------
{| {P} l_1 => t_1; ...; l_n => t_n |} : (e : {| l_1 ... l_n |}) -> P e
```

Example of usage.
```
let -sum : {A : *} -> (A -> *) -> * = \{A} K. (x : A) ** K x;
let -Sum = \A B. sum {| Left => A; Right => B |};
let Left : {-A -B : *} -> A -> Sum A B = \x. ('Left, x);
let Right : {-A -B : *} -> B -> Sum A B = \x. ('Right, x);

let -Nat = Data \Nat. sum {| Z => (); S => Nat |};
let -List = \A. Data \ListA. sum {| Nil => (); Cons => A ** ListA |};
let -Vec = \A. IData \VecA n. sum {| VNil => Eq Z n; VCons => (-m : Nat) ** A ** VecA m ** Eq (S m) n |};
```

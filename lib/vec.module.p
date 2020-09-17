import lib/unit.p
import lib/nat.p

def VecModule =
  {Vec : (i : Nat) -> * -> *}
  **
  (VNil : {t : *} -> Vec Z t)
  **
  (VCons : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t)
  **
  (genindVec :
    {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> (({i : Nat} -> (x : Vec i t) -> P i x) -> {n : Nat} -> (hd : t) -> (y : Vec n t) -> P (S n) (VCons {t} {n} hd y))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x)
  **
  UnitType

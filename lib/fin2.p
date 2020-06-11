import lib/void.p
import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p

def FinF =
  \(r : Nat -> *) (n : Nat).
    {m : Nat} ** Eq m n ** (caseNat m
      Void
      (\n. Sum UnitType (r n)))
def Fin = IFix Nat FinF
def FZ
  : {n : Nat} -> Fin (S n)
  = \{n}. IIn {Nat} {FinF} {S n}
      (InL {UnitType} {Fin n} ())
def FS
  : {n : Nat} -> Fin n -> Fin (S n)
  = \{n} f. IIn {Nat} {FinF} {S n}
      (InR {UnitType} {Fin n} f)

def genindFin
  : {P : (i : Nat) -> Fin i -> *}
    -> ({n : Nat} -> P (S n) (FZ {n}))
    -> (({i : Nat} -> (x : Fin i) -> P i x) -> {n : Nat} -> (y : Fin n) -> P (S n) (FS {n} y))
    -> {n : Nat}
    -> (x : Fin n)
    -> P n x
  = \{P} fz fs {n} x. genindIFix {Nat} {FinF} {P}
      (\rec {i} z. _x)
      {n} x

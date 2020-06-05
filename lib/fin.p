import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p

def FinF = \(r : Nat -> *) (n : Nat). Sum ({m : Nat} ** Eq Nat (S m) n) ({m : Nat} ** r m ** Eq Nat (S m) n)
def Fin = IFix Nat FinF
def FZ
  : {n : Nat} -> Fin (S n)
  = \{n}. IIn {Nat} {FinF} {S n}
      (InL {{m : Nat} ** Eq Nat (S m) (S n)} {_} ({n}, refl {Nat} {S n}))
def FS
  : {n : Nat} -> Fin n -> Fin (S n)
  = \{n} f. IIn {Nat} {FinF} {S n}
      (InR {_} {{m : Nat} ** Fin m ** Eq Nat (S m) (S n)} ({n}, f, refl {Nat} {S n}))

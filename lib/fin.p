import lib/unit.p
import lib/nat.p

def FinD = data Nat
  (\R. ({n : Nat} ** UnitType, \a _ E. E (S a.fst)))
  (\R. ({n : Nat} ** R n, \a _ E. E (S a.fst)))
def Fin : Nat -> * = \n. tcon FinD n
def FZ : {n : Nat} -> Fin (S n) = \{n}. con 0 {FinD} ({n}, ())
def FS : {n : Nat} -> Fin n -> Fin (S n) = \{n} f. con 1 {FinD} ({n}, f)

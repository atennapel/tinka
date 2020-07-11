import lib/nat.p

def Fin : Nat -> * = %Fin
def FZ : {n : Nat} -> Fin (S n) = %FZ
def FS : {n : Nat} -> Fin n -> Fin (S n) = %FS
def elimFin
  : {P : (n : Nat) -> Fin n -> *}
    -> ({m : Nat} -> P (S m) (FZ {m}))
    -> ({m : Nat} -> (y : Fin m) -> P (S m) (FS {m} y))
    -> {n : Nat} -> (x : Fin n) -> P n x
  = %elimFin

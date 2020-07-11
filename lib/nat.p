import lib/rec.p

def Nat : * = %Nat
def Z : Nat = %Z
def S : Nat -> Nat = %S
def elimNat : {P : Nat -> *} -> P Z -> ((m : Nat) -> P (S m)) -> (n : Nat) -> P n = %elimNat

def caseNat : {t : *} -> Nat -> t -> (Nat -> t) -> t = \{t} n z s. elimNat {\_. t} z s n

def pred : Nat -> Nat = \n. caseNat n 0 (\m. m)

def indNat
  : {P : Nat -> *} -> P 0 -> ({m : Nat} -> P m -> P (S m)) -> (n : Nat) -> P n
  = \{P} z s. drec {Nat} {P} \r n. elimNat {P} z (\m. s {m} (r m)) n

def cataNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \{t} n z s. indNat {\_. t} z (\{_}. s) n

def add : Nat -> Nat -> Nat = \a b. cataNat a b S

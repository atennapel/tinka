def Nat = data N. N | N -> N
def Z : Nat = con {Nat} 0 2
def S : Nat -> Nat = \n. con {Nat} 1 2 n

def caseNat
  : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \{t} n z s. case {Nat} {\_. t} n (\_. z) (\_. s)

def dcaseNat
  : {P : Nat -> *} -> (n : Nat) -> P Z -> ((m : Nat) -> P (S m)) -> P n
  = \{P} n z s. case {Nat} {P} n (\_. z) (\_. s)

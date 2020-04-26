import lib/prim.p

def Nat = data N. N | N -> N
def Z : Nat = con {Nat} 0 2
def S : Nat -> Nat = \n. con {Nat} 1 2 n

def indNat
  : {P : Nat -> *} -> P Z -> ((m : Nat) -> P m -> P (S m)) -> (n : Nat) -> P n
  = \{P} z s n. case {Nat} {P} n (\_. z) (\rec m. s m (rec m))

def caseNat
  : {t : *} -> t -> (Nat -> t) -> Nat -> t
  = \{t} z s n. case {Nat} {\_. t} n (\_. z) (\_. s)

def recNat
  : {t : *} -> t -> (Nat -> t -> t) -> Nat -> t
  = \{t} z s n. indNat {\_. t} z s n

def foldNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \{t} n z s. recNat {t} z (\_. s) n

def toPrimNat : Nat -> PrimNat = \n. foldNat n PrimNatZ PrimNatS
def toPrimChar : Nat -> PrimChar = toPrimNat

def pred : Nat -> Nat = \n. caseNat Z (\m. m) n

def add : Nat -> Nat -> Nat = \n m. foldNat n m S
def mul : Nat -> Nat -> Nat = \n m. foldNat n Z (add m)
def pow : Nat -> Nat -> Nat = \n m. foldNat m (S Z) (mul n)

def sub : Nat -> Nat -> Nat = \n m. foldNat m n pred

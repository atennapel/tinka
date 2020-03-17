import lib/fix.p

def NatF = \(r : *). {t : *} -> t -> (r -> t) -> t
def Nat = Fix NatF
def Z : Nat = In {NatF} \z s. z
def S : Nat -> Nat = \n. In {NatF} \z s. s n

def foldNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \n z s. fold {NatF} (\rc m. m z (\x. s (rc x))) n

def add : Nat -> Nat -> Nat = \n m. foldNat n m S

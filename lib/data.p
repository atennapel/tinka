import lib/unit.p

def NatD = data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
def Nat = tcon NatD ()
def Z : Nat = con 0 NatD ()
def S : Nat -> Nat = \n. con 1 NatD n

def ListD = \t. data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (t ** R (), \_ _ E. E ()))
def List = \t. tcon (ListD t) ()
def Nil : {t : *} -> List t = \{t}. con 0 (ListD t) ()
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. con 1 (ListD t) (hd, tl)

def VecD = \t. data Nat
  (\R. (UnitType, \_ _ E. E Z))
  (\R. ({n : Nat} ** t ** R n, \a _ E. E (S a.fst)))
def Vec : Nat -> * -> * = \n t. tcon (VecD t) n
def VNil : {t : *} -> Vec Z t = \{t}. con 0 (VecD t) ()
def VCons : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t = \{t} {n} hd tl. con 1 (VecD t) ({n}, hd, tl)

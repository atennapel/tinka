import lib/fix.p

def NatF = \(r : *). {t : *} -> t -> (r -> t) -> t
def Nat = Fix NatF
def Z : Nat = In {NatF} \z s. z
def S : Nat -> Nat = \n. In {NatF} \z s. s n

def caseNat : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \n z s. caseFix {NatF} n z s
def recNat : {t : *} -> Nat -> t -> ((Nat -> t) -> Nat -> t) -> t
  = \{t} n z s. fold {NatF} {t} (\rec m. m {t} z (\k. s rec k)) n

def foldNat : {t : *} -> Nat -> t -> (t -> t) -> t
  = \n z s. recNat n z (\rec m. s (rec m))

def pred : Nat -> Nat = \n. caseNat n Z (\n. n)

def add : Nat -> Nat -> Nat = \n m. foldNat n m S
def mul : Nat -> Nat -> Nat = \n m. foldNat n Z (add m)
def pow : Nat -> Nat -> Nat = \n m. foldNat m (S Z) (mul n)

def sub : Nat -> Nat -> Nat = \n m. foldNat m n pred

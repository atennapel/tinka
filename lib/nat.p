import lib/fix.p
import lib/maybe.p

def NatD = MaybeD
def Nat = Fix NatD
def Z : Nat = In {NatD} (True, ())
def S : Nat -> Nat = \n. In {NatD} (False, (n, ()))

-- def caseNat
--  : {t : *} -> Nat -> t -> (Nat -> t) -> t
--  = \{t} n z s. indSigma {Bool} {\b. if b UnitType Nat} {\_. Nat} (\b. indBool {\b. if b UnitType Nat -> Nat} (\_. Z) (\n. n) b) (out NatD n)

-- def pred : Nat -> Nat = \n. caseNat n Z (\n. n)

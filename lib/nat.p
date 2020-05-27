import lib/unit.p
import lib/bool.p
import lib/sigma.p
import lib/fix.p

def NatD = Arg {Bool} \b. if b End (Rec End)
def Nat = Fix NatD
def Z : Nat = In {NatD} (True, ())
def S : Nat -> Nat = \n. In {NatD} (False, (n, ()))

-- def caseNat
--   : {t : *} -> Nat -> t -> (Nat -> t) -> t
--   = \{t} n z s. indSigma {Bool} {\b. if b UnitType (Nat ** UnitType)} {\_. t} (\b. indBool {\b. if b UnitType (Nat ** UnitType) -> t} (\_. z) (\n. s (fst n)) b) (out NatD n)

-- def pred : Nat -> Nat = \n. caseNat n Z (\n. n)

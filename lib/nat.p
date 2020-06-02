import lib/unit.p
import lib/sum.p
import lib/fix.p

def NatF = \(r : *). Sum UnitType r
def Nat = Fix NatF
def Z : Nat = In {NatF} (InL Unit)
def S : Nat -> Nat = \n. In {NatF} (InR n)

def caseNat
  : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \n z s. caseSum (outFix n) (\_. z) s

def cataNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \{t} n z s. mendlerFix {NatF} {t} (\rec y. caseSum y (\_. z) (\n. s (rec n))) n

def pred : Nat -> Nat = \n. caseNat n Z (\n. n)
def add : Nat -> Nat -> Nat = \a b. cataNat a b S

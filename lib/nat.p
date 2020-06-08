import lib/unit.p
import lib/sum.p
import lib/fix.p

def NatF = \(r : *). Sum UnitType r
def Nat = Fix NatF
def Z : Nat = In {NatF} (InL ())
def S : Nat -> Nat = \n. In {NatF} (InR n)

def caseNat
  : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \n z s. caseSum (outFix n) (\_. z) s

def cataNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \{t} n z s. mendlerFix {NatF} {t} (\rec y. caseSum y (\_. z) (\n. s (rec n))) n

def paraNat
  : {t : *} -> Nat -> t -> (Nat -> t -> t) -> t
  = \{t} n z s. genrecFix {NatF} {t} (\rec y. caseSum y (\_. z) (\n. s n (rec n))) n

def recNat
  : {t : *} -> Nat -> t -> ((Nat -> t) -> Nat -> t) -> t
  = \{t} n z s. genrecFix {NatF} {t} (\rec y. caseSum y (\_. z) (\n. s rec n)) n

def indNat
  : {P : Nat -> *}
    -> P Z
    -> ({m : Nat} -> P m -> P (S m))
    -> (n : Nat)
    -> P n
  = \{P} z s n. genindFix {NatF} {P}
    (\rec y. indSum {UnitType} {Nat} {\s. P (In {NatF} s)} (\_. z) (\m. s {m} (rec m)) y)
    n

def pred : Nat -> Nat = \n. caseNat n Z (\n. n)
def add : Nat -> Nat -> Nat = \a b. cataNat a b S

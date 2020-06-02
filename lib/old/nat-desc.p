import lib/unit.p
import lib/bool.p
import lib/sigma.p
import lib/fix.p

def NatD = Arg {Bool} \b. if b End (Rec End)
def Nat = Fix NatD
def Z : Nat = In {NatD} (True, ())
def S : Nat -> Nat = \n. In {NatD} (False, (n, ()))

def caseNatR
  : {a b : *} -> interpDesc NatD a -> b -> (a -> b) -> b
  = \{a} {b} n z s. genCase NatD {a} {b} n (\d. indBool {\d. CasesDesc (if d End (Rec End)) a b} z s d)

def caseNat
  : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \{t} n z s. caseNatR {Nat} {t} (out NatD n) z s

def pred : Nat -> Nat = \n. caseNat n Z (\m. m)

def indNat
  : {P : Nat -> *} -> (n : Nat) -> P Z -> ({m : Nat} -> P m -> P (S m)) -> P n
  = \{P} n z s. indFix NatD n {P} (\c r. indSigma )

def cataNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \{t} n z s. cataFix NatD {t} (\c. caseNatR {t} {t} c z s) n

def add : Nat -> Nat -> Nat = \a b. cataNat a b S

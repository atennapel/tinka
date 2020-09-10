import lib/unit.p
import lib/eq.p
import lib/bool.p
import lib/monoid.p
import lib/eqb.p

def NatD = data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
def Nat = tcon NatD ()
def Z : Nat = con 0 {NatD} ()
def S : Nat -> Nat = \n. con 1 {NatD} n

def genindNat
  : {P : Nat -> *}
    -> P Z
    -> (((m : Nat) -> P m) -> (m : Nat) -> P (S m))
    -> (n : Nat)
    -> P n
  = \{P} z s n. elim {NatD} {\_. P} {()} n (\_ _. z) (\rec m. s (rec {()}) m)

def indNat
  : {P : Nat -> *}
    -> P Z
    -> ({m : Nat} -> P m -> P (S m))
    -> (n : Nat)
    -> P n
  = \{P} z s n. genindNat {P} z (\rec m. s {m} (rec m)) n

def dcaseNat
  : {P : Nat -> *} -> (n : Nat) -> P Z -> ((m : Nat) -> P (S m)) -> P n
  = \{P} n z s. genindNat {P} z (\_. s) n

def recNat
  : {t : *} -> Nat -> t -> ((Nat -> t) -> Nat -> t) -> t
  = \{t} n z s. genindNat {\_. t} z s n

def caseNat
  : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \n z s. recNat n z (\_. s)

def cataNat
  : {t : *} -> Nat -> t -> (t -> t) -> t
  = \n z s. recNat n z (\rec n. s (rec n))

def paraNat
  : {t : *} -> Nat -> t -> (Nat -> t -> t) -> t
  = \n z s. recNat n z (\rec n. s n (rec n))

def pred : Nat -> Nat = \n. caseNat n Z (\n. n)
def add : Nat -> Nat -> Nat = \a b. cataNat a b S
def mul : Nat -> Nat -> Nat = \a b. cataNat a Z (add b)

def monoidNatAdd : Monoid Nat = mkMonoid Z add
def monoidNatMul : Monoid Nat = mkMonoid (S Z) mul

def eqNat : Nat -> Nat -> Bool = \a. recNat a (\b. caseNat b True (\_. False)) (\rec x b. caseNat b False (rec x))
def eqbNat : Eqb Nat = eqNat

def pred_eq
  : {n : Nat} -> {m : Nat} -> Eq n (S m) -> Eq n (S (pred n))
  = \{n} {m} p.
    let q = (lift {_} {_} {pred} p : Eq (pred n) m) in
    let sq = symm q in
    rewrite {_} {\x. Eq n (S x)} sq p

def pred_eq_symm
  : {n : Nat} -> Eq n (S (pred n)) -> {m : Nat} ** Eq n (S m)
  = \{n} p. ({pred n}, p)

def eq_S
  : {n m : Nat} -> Eq n m -> Eq (S n) (S m)
  = \e. lift {_} {_} {S} e

def eq_S_symm
  : {n m : Nat} -> Eq (S n) (S m) -> Eq n m
  = \e. lift {_} {_} {pred} e

def isZero : Nat -> Bool = \n. caseNat n True (\_. False)

def z_neq_S
  : {n : Nat} -> Neq Z (S n)
  = \{n} eq. rewrite {_} {\n. liftBool (isZero n)} eq Unit
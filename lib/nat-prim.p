import lib/eq.p
import lib/bool.p

def Nat = %Nat

def add = %addNat
def sub = %subNat
def mul = %mulNat
def div = %divNat
def mod = %modNat
def pow = %powNat
def eqNat = %eqNat
def ltNat = %ltNat
def lteqNat = %lteqNat

def gtNat = \a b. not (lteqNat a b)
def gteqNat = \a b. not (ltNat a b)
def isZero = \n. eqNat n 0

def Z : Nat = 0
def S : Nat -> Nat = \n. add n 1
def pred : Nat -> Nat = \n. sub n 1

def genindNatFull
  : {P : Nat -> *}
    -> (((m : Nat) -> P m) -> P 0)
    -> (((m : Nat) -> P m) -> (m : Nat) -> P (S m))
    -> (n : Nat)
    -> P n
  = %genindNat

def genindNat
  : {P : Nat -> *}
    -> P 0
    -> (((m : Nat) -> P m) -> (m : Nat) -> P (S m))
    -> (n : Nat)
    -> P n
  = \{P} z s n. genindNatFull {P} (\_. z) s n

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

-- def pred_eq
--  : {n : Nat} -> {m : Nat} -> Eq n (S m) -> Eq n (S (pred n))
--  = \{n} {m} p.
--    let q = (lift {_} {_} {pred} p : Eq (pred n) m) in
--    let sq = symm q in
--    rewrite {_} {\x. Eq n (S x)} sq p

-- def pred_eq_symm
--  : {n : Nat} -> Eq n (S (pred n)) -> {m : Nat} ** Eq n (S m)
--  = \{n} p. ({pred n}, p)

-- def eq_S
--  : {n m : Nat} -> Eq n m -> Eq (S n) (S m)
--  = \e. lift {_} {_} {S} e 

-- def eq_S_symm
--  : {n m : Nat} -> Eq (S n) (S m) -> Eq n m
--  = \e. lift {_} {_} {pred} e

-- def z_neq_S
--  : {n : Nat} -> Neq Z (S n)
--  = \{n} eq. rewrite {_} {\n. liftBool (isZero n)} eq Unit

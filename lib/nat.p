def Nat = %Nat
def Z : Nat = 0
def S : Nat -> Nat = %S

def genindNat
  : {P : Nat -> *}
    -> P Z
    -> (((k : Nat) -> P k) -> (m : Nat) -> P (S m))
    -> (n : Nat)
    -> P n
  = %genindNat

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

import lib/unit.p
import lib/eq.p
import lib/bool.p
import lib/monoid.p
import lib/eqb.p
import lib/nat.p

def monoidNatAdd : Monoid Nat = mkMonoid Z add
def monoidNatMul : Monoid Nat = mkMonoid (S Z) mul

def eqNat : Nat -> Nat -> Bool = \a. recNat a (\b. caseNat b True (\_. False)) (\rec x b. caseNat b False (rec x))
def eqbNat : Eqb Nat = eqNat

def ltNat : Nat -> Nat -> Bool = \a.
  recNat a (\b. caseNat b False (\_. True)) (\rec x b. caseNat b False (rec x))

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

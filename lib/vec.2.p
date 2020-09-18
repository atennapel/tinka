import lib/void.p
import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p
import lib/maybe.p
import lib/nat.extra.p
-- work in progress
-- implementation of Vec without having to store the proofs
import lib/vec.module.p

def VecF = \(t : *) (r : Nat -> *) (i : Nat). caseNat i UnitType (\m. t ** r m)
def Vec = \(n : Nat) (t : *). IFix Nat (VecF t) n
def VNil : {t : *} -> Vec Z t = \{t}. IIn {Nat} {VecF t} {Z} ()
def VCons
  : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t
  = \{t} {n} hd tl. IIn {Nat} {VecF t} {S n} (hd, tl)

def eq_Z_unit
  : {t : *} -> (i : Nat) -> Eq i Z -> (x : VecF t (IFix Nat (VecF t)) i) -> HEq x ()
  = \{t} i q. indNat {\i. Eq i Z -> (x : VecF t (IFix Nat (VecF t)) i) -> HEq x ()} (\_ x. Refl) (\{m} _ p _. caseVoid (z_neq_S {m} (symm p))) i q

--def eq_Z_VNil
--  : {t : *} -> (x : Vec Z t) -> Eq x VNil
--  = \{t} x. genindIFix {Nat} {VecF t} {\i f. Eq i Z -> HEq f (VNil {t})} (\rec {i} x q. let xx = rewrite {Nat} {\i. VecF t (IFix Nat (VecF t)) i} q x in _y) x Refl

def genindVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> (({i : Nat} -> (x : Vec i t) -> P i x) -> {n : Nat} -> (hd : t) -> (y : Vec n t) -> P (S n) (VCons {t} {n} hd y))
    -> (n : Nat)
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs n. indNat {\n. (x : Vec n t) -> P n x}
      (\x. genindIFix {Nat} {VecF t} {\i f. Eq i Z -> P i f} (\rec {i} z p. _z) {Z} x Refl)
      _s n

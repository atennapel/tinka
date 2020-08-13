import lib/void.p
import lib/unit.p
import lib/nat.p
import lib/eq.p
import lib/maybe.p
import lib/rec.p

def VecD = \t. data Nat
  (\R. (UnitType, \_ _ E. E Z))
  (\R. ({n : Nat} ** t ** R n, \a _ E. E (S a.fst)))
def Vec : Nat -> * -> * = \n t. tcon (VecD t) n
def VNil : {t : *} -> Vec Z t = \{t}. con 0 (VecD t) ()
def VCons : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t = \{t} {n} hd tl. con 1 (VecD t) ({n}, hd, tl)

def dcaseVec
  : {t : *}
    -> {P : (n : Nat) -> Vec n t -> *}
    -> P Z VNil
    -> ({m : Nat} -> (hd : t) -> (tl : Vec m t) -> P (S m) (VCons hd tl))
    -> {n : Nat} -> (v : Vec n t) -> P n v
  = \{t} {P} n c {m} v. elim (VecD t) P m v (\_. n) (\p. c {p.fst} p.snd.fst p.snd.snd)

def caseVec
  : {n : Nat} -> {t : *} -> {r : *} -> Vec n t -> r -> ({m : Nat} -> t -> Vec m t -> r) -> r
  = \{n} {t} {r} v nil c. dcaseVec {t} {\_ _. r} nil c {n} v

def genindVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> (({i : Nat} -> (x : Vec i t) -> P i x) -> {n : Nat} -> (hd : t) -> (y : Vec n t) -> P (S n) (VCons {t} {n} hd y))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs. dreci {Nat} {\n. (v : Vec n t) -> P n v} \rec {n} v.
      dcaseVec {t} {P} fz (\{m} hd tl. fs rec {m} hd tl) {n} v

def indVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> ({n : Nat} -> {tl : Vec n t} -> (hd : t) -> P n tl -> P (S n) (VCons {t} {n} hd tl))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs {n} x. genindVec {t} {P} fz (\rec {n} hd tl. fs {n} {tl} hd (rec tl)) {n} x

def recVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> (({i : Nat} -> Vec i t -> r) -> {n : Nat} -> t -> Vec n t -> r) -> r
  = \{t} {r} {n} x fz fs. genindVec {t} {\_ _. r} fz fs {n} x

def cataVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> (t -> r -> r) -> r
  = \{t} {r} {n} x fz fs. recVec x fz (\rec {n} hd tl. fs hd (rec {n} tl))

def paraVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> ({n : Nat} -> t -> Vec n t -> r -> r) -> r
  = \{t} {r} {n} x fz fs. recVec x fz (\rec {n} hd tl. fs {n} hd tl (rec {n} tl))

def mapVec
  : {a b : *} -> {n : Nat} -> (a -> b) -> Vec n a -> Vec n b
  = \{a} {b} f l. indVec {a} {\i _. Vec i b} (VNil {b}) (\hd tl. VCons (f hd) tl) l

def unknownHeadVec
  : {t : *} -> {n : Nat} -> Vec n t -> Maybe t
  = \{t} l. caseVec l (Nothing {t}) (\hd _. Just hd)

def eq_Z_VNil
  : {t : *} -> (x : Vec Z t) -> Eq x VNil
  = \{t} x. (dcaseVec {t} {\i v. Eq Z i -> HEq v (VNil {t})} (\_. Refl) (\_ _ q. caseVoid (z_neq_S q)) x) (Refl {_} {Z})

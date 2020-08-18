import lib/void.p
import lib/unit.p
import lib/nat.p
import lib/eq.p
import lib/maybe.p
import lib/functor.p

def VecD = \t. data Nat
  (\R. (UnitType, \_ _ E. E Z))
  (\R. ({n : Nat} ** t ** R n, \a _ E. E (S a.fst)))
def Vec : Nat -> * -> * = \n t. tcon (VecD t) n
def VNil : {t : *} -> Vec Z t = \{t}. con 0 {VecD t} ()
def VCons : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t = \{t} {n} hd tl. con 1 {VecD t} ({n}, hd, tl)

def genindVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> (({i : Nat} -> (x : Vec i t) -> P i x) -> {n : Nat} -> (hd : t) -> (y : Vec n t) -> P (S n) (VCons {t} {n} hd y))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs {n} x. elim {VecD t} {P} {n} x (\_ _. fz) (\rec p. fs rec {p.fst} p.snd.fst p.snd.snd)

def indVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> ({n : Nat} -> {tl : Vec n t} -> (hd : t) -> P n tl -> P (S n) (VCons {t} {n} hd tl))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs {n} x. genindVec {t} {P} fz (\rec {n} hd tl. fs {n} {tl} hd (rec tl)) {n} x

def dcaseVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> ({n : Nat} -> (hd : t) -> (tl : Vec n t) -> P (S n) (VCons {t} {n} hd tl))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs {n} x. genindVec {t} {P} fz (\_. fs) {n} x

def recVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> (({i : Nat} -> Vec i t -> r) -> {n : Nat} -> t -> Vec n t -> r) -> r
  = \{t} {r} {n} x fz fs. genindVec {t} {\_ _. r} fz fs {n} x

def caseVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> ({n : Nat} -> t -> Vec n t -> r) -> r
  = \{t} {r} {n} x fz fs. recVec x fz (\_. fs)

def cataVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> (t -> r -> r) -> r
  = \{t} {r} {n} x fz fs. recVec x fz (\rec {n} hd tl. fs hd (rec {n} tl))

def paraVec
  : {t r : *} -> {n : Nat} -> Vec n t -> r -> ({n : Nat} -> t -> Vec n t -> r -> r) -> r
  = \{t} {r} {n} x fz fs. recVec x fz (\rec {n} hd tl. fs {n} hd tl (rec {n} tl))

def mapVec
  : {n : Nat} -> {a b : *} -> (a -> b) -> Vec n a -> Vec n b
  = \{n} {a} {b} f l. indVec {a} {\i _. Vec i b} (VNil {b}) (\hd tl. VCons (f hd) tl) l

def functorVec : {n : Nat} -> Functor (Vec n) = \{n}. mapVec {n}

def unknownHeadVec
  : {t : *} -> {n : Nat} -> Vec n t -> Maybe t
  = \{t} l. caseVec l (Nothing {t}) (\hd _. Just hd)

def eq_Z_VNil
  : {t : *} -> (x : Vec Z t) -> Eq x VNil
  = \{t} x. (dcaseVec {t} {\i v. Eq Z i -> HEq v (VNil {t})} (\_. Refl) (\_ _ q. caseVoid (z_neq_S q)) x) (Refl {_} {Z})

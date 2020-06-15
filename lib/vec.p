import lib/void.p
import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p
import lib/maybe.p

def VecF = \(t : *) (r : Nat -> *) (i : Nat). Sum (Eq {Nat} Z i) ({m : Nat} ** t ** r m ** Eq {Nat} (S m) i)
def Vec = \(n : Nat) (t : *). IFix Nat (VecF t) n
def VNil : {t : *} -> Vec Z t = \{t}. IIn {Nat} {VecF t} {Z} (InL (Refl {Nat} {Z}))
def VCons
  : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t
  = \{t} {n} hd tl. IIn {Nat} {VecF t} {S n} (InR {_} {{m : Nat} ** t ** Vec m t ** Eq {Nat} (S m) (S n)} ({n}, hd, tl, Refl {Nat} {S n}))

def genindVec
  : {t : *}
    -> {P : (i : Nat) -> Vec i t -> *}
    -> P Z (VNil {t})
    -> (({i : Nat} -> (x : Vec i t) -> P i x) -> {n : Nat} -> (hd : t) -> (y : Vec n t) -> P (S n) (VCons {t} {n} hd y))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} fz fs {n} x. genindIFix {Nat} {VecF t} {P}
      (\rec {i} z.
        indSum
        {Eq {Nat} Z i}
        {{m : Nat} ** t ** Vec m t ** Eq {Nat} (S m) i}
        {\s. P i (IIn {Nat} {VecF t} {i} s)}
        (\q. elimEq {_} {_} {\z e. P z (IIn {Nat} {VecF t} {z} (InL e))} fz q)
        (\p.
          let {mm} = p.0 in
          let hd = p.1 in
          let tl = p.2 in
          let q = p.snd.snd.snd in
          elimEq {_} {_} {\j e. P j (IIn {Nat} {VecF t} {j} (InR {_} {{m : Nat} ** t ** Vec m t ** Eq {Nat} (S m) j} ({mm}, hd, tl, e)))} (fs rec {mm} hd tl) q)
        z)
      {n} x

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
  : {a b : *} -> {n : Nat} -> (a -> b) -> Vec n a -> Vec n b
  = \{a} {b} f l. indVec {a} {\i _. Vec i b} (VNil {b}) (\hd tl. VCons (f hd) tl) l

def unknownHeadVec
  : {t : *} -> {n : Nat} -> Vec n t -> Maybe t
  = \{t} l. caseVec l (Nothing {t}) (\hd _. Just hd)

def eq_Z_VNil
  : {t : *} -> (x : Vec Z t) -> Eq x VNil
  = \{t} x. (dcaseVec {t} {\i v. Eq Z i -> HEq v (VNil {t})} (\_. Refl) (\_ _ q. caseVoid (z_neq_S q)) x) (Refl {_} {Z})

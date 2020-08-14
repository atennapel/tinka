import lib/unit.p
import lib/nat.p

def FinD = data Nat
  (\R. ({n : Nat} ** UnitType, \a _ E. E (S a.fst)))
  (\R. ({n : Nat} ** R n, \a _ E. E (S a.fst)))
def Fin : Nat -> * = \n. tcon FinD n
def FZ : {n : Nat} -> Fin (S n) = \{n}. con 0 {FinD} ({n}, ())
def FS : {n : Nat} -> Fin n -> Fin (S n) = \{n} f. con 1 {FinD} ({n}, f)

def genindFin
  : {P : (i : Nat) -> Fin i -> *}
    -> ({n : Nat} -> P (S n) (FZ {n}))
    -> (({i : Nat} -> (x : Fin i) -> P i x) -> {n : Nat} -> (y : Fin n) -> P (S n) (FS {n} y))
    -> {n : Nat}
    -> (x : Fin n)
    -> P n x
  = \{P} fz fs {n} x. elim {FinD} {P} {n} x (\_ p. fz {p.fst}) (\rec p. fs rec {p.fst} p.snd)

def indFin
  : {P : (i : Nat) -> Fin i -> *}
    -> ({n : Nat} -> P (S n) (FZ {n}))
    -> ({n : Nat} -> {y : Fin n} -> P n y -> P (S n) (FS {n} y))
    -> {n : Nat}
    -> (x : Fin n)
    -> P n x
  = \{P} z s {n} x. genindFin {P} z (\rec {n} y. s {n} {y} (rec y)) {n} x

def dcaseFin
  : {P : (i : Nat) -> Fin i -> *}
    -> ({n : Nat} -> P (S n) (FZ {n}))
    -> ({n : Nat} -> (y : Fin n) -> P (S n) (FS {n} y))
    -> {n : Nat}
    -> (x : Fin n)
    -> P n x
  = \{P} z s {n} x. genindFin {P} z (\_ {n} y. s {n} y) {n} x

def recFin
  : {t : *} -> {n : Nat} -> Fin n -> t -> (({i : Nat} -> Fin i -> t) -> {n : Nat} -> Fin n -> t) -> t
  = \{t} x z s. genindFin {\_ _. t} (\{_}. z) s x

def caseFin
  : {t : *} -> {n : Nat} -> Fin n -> t -> ({n : Nat} -> Fin n -> t) -> t
  = \{t} x z s. recFin x z (\_. s)

def cataFin
  : {t : *} -> {n : Nat} -> Fin n -> t -> (t -> t) -> t
  = \{t} x z s. recFin x z (\rec r. s (rec r))

def paraFin
  : {t : *} -> {n : Nat} -> Fin n -> t -> ({n : Nat} -> Fin n -> t -> t) -> t
  = \{t} x z s. recFin x z (\rec {n} r. s {n} r (rec r))

def finToNat
  : {n : Nat} -> Fin n -> Nat
  = \x. cataFin x Z S

def finZVoid
  : Fin Z -> Void
  = \x. (indFin {\i _. Eq Z i -> Void} z_neq_S (\_. z_neq_S) x) (Refl {_} {Z})

import lib/void.p
import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p

def FinF = \(r : Nat -> *) (n : Nat). Sum ({m : Nat} ** Eq {Nat} (S m) n) ({m : Nat} ** r m ** Eq {Nat} (S m) n)
def Fin = IFix Nat FinF
def FZ
  : {n : Nat} -> Fin (S n)
  = \{n}. IIn {Nat} {FinF} {S n}
      (InL {{m : Nat} ** Eq {Nat} (S m) (S n)} {_} ({n}, Refl {Nat} {S n}))
def FS
  : {n : Nat} -> Fin n -> Fin (S n)
  = \{n} f. IIn {Nat} {FinF} {S n}
      (InR {_} {{m : Nat} ** Fin m ** Eq {Nat} (S m) (S n)} ({n}, f, Refl {Nat} {S n}))

def genindFin
  : {P : (i : Nat) -> Fin i -> *}
    -> ({n : Nat} -> P (S n) (FZ {n}))
    -> (({i : Nat} -> (x : Fin i) -> P i x) -> {n : Nat} -> (y : Fin n) -> P (S n) (FS {n} y))
    -> {n : Nat}
    -> (x : Fin n)
    -> P n x
  = \{P} fz fs {n} x. genindIFix {Nat} {FinF} {P}
      (\rec {i} z.
        indSum
        {{m : Nat} ** Eq {Nat} (S m) i}
        {{m : Nat} ** Fin m ** Eq {Nat} (S m) i}
        {\s. P i (IIn {Nat} {FinF} {i} s)}
        (\p.
          let {pm} = p.fst in
          elimEq {_} {_} {\mm e. P mm (IIn {Nat} {FinF} {mm} (InL {{m : Nat} ** Eq {Nat} (S m) mm} {_} ({pm}, e)))} (fz {pm}) p.snd)
        (\p.
          let {pm} = p.0 in
          let rr = p.1 in
          let q = p.snd.snd in
          elimEq {_} {_} {\mm e. P mm (IIn {Nat} {FinF} {mm} (InR {_} {{m : Nat} ** Fin m ** Eq {Nat} (S m) mm} ({pm}, rr, e)))} (fs rec {pm} rr) q)
        z)
      {n} x

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

def finCaseResult
  : (n : Nat) -> Fin n -> *
  = \n. dcaseNat {\n. Fin n -> *} n
      (\x. {P : Fin 0 -> *} -> P x)
      (\m x. {P : Fin (S m) -> *} -> P (FZ {m}) -> ((y : Fin m) -> P (FS {m} y)) -> P x)

def caseNFin
  : {n : Nat} -> (f : Fin n) -> finCaseResult n f
  = \{n} f.
    dcaseFin {finCaseResult} (\{m} {P} z s. z) (\{m} y {P} z s. s y) {n} f 

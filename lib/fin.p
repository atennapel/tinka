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
          let pp = p.snd in
          let f = (fz {pm} : P (S pm) (IIn {Nat} {FinF} {S pm} (InL {{m : Nat} ** Eq {Nat} (S m) (S pm)} {_} ({pm}, Refl {Nat} {S pm})))) in
          --let refl = rewrite {_} {\x. Eq {Nat} (S pm) x} pp (Refl {_} {S pm}) in
          --let uipx = uip refl pp in
          --let uipfixed = eqJ {_} {\a b pi. HEq (Refl {Nat} {a}) pi} (\{x}. Refl) pp in
          --let uipfixedrewr = rewriteBoth {_} {\spm j qq. HEq {Eq {Nat} (S pm) (S pm)} (Refl {Nat} {S pm}) qq} pp uipfixed in
          let xxx = rewrite {_} {\x. {m : Nat} ** Eq {Nat} (S m) x} (symm pp) p in
          _x)
        (\p. _y)
        z)
      {n} x

def recFin
  : {n : Nat} -> {t : *} -> Fin n -> ({m : Nat} -> Eq {Nat} (S m) n -> t) -> (({k : Nat} -> Fin k -> t) -> {m : Nat} -> Fin m -> Eq {Nat} (S m) n -> t) -> t
  = \{n} {t} x z s. genrecIFix {Nat} {FinF} {t} (\rec {i} y. caseSum y (\p. z {p.fst} p.snd) (\p. s rec {p.fst} p.snd.fst p.snd.snd)) {n} x

def caseFin
  : {n : Nat} -> {t : *} -> Fin n -> ({m : Nat} -> Eq {Nat} (S m) n -> t) -> ({m : Nat} -> Fin m -> Eq {Nat} (S m) n -> t) -> t
  = \{n} {t} f z s. caseSum (outIFix f) (\p. z {p.fst} p.snd) (\p. s {p.fst} p.snd.fst p.snd.snd)

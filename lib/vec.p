import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p

def VecF = \(t : *) (r : Nat -> *) (i : Nat). Sum (Eq {Nat} Z i) ({m : Nat} ** t ** r m ** Eq {Nat} (S m) i)
def Vec = \(n : Nat) (t : *). IFix Nat (VecF t) n
def VNil : {t : *} -> Vec Z t = \{t}. IIn {Nat} {VecF t} {Z} (InL (refl {Nat} {Z}))
def VCons
  : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t
  = \{t} {n} hd tl. IIn {Nat} {VecF t} {S n} (InR {_} {{m : Nat} ** t ** Vec m t ** Eq {Nat} (S m) (S n)} ({n}, hd, tl, refl {Nat} {S n}))

def genindFin
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
        (\q. rewrite {_} {\j. P j (IIn {Nat} {VecF t} {j} (InL {Eq {Nat} Z j} {_} (_q)))} q fz)
        (\p. _y)
        z)
      {n} x

import lib/unit.p
import lib/sum.p
import lib/ifix.p
import lib/nat.p
import lib/eq.p

def VecF = \(t : *) (r : Nat -> *) (i : Nat). Sum (Eq {Nat} Z i) ({m : Nat} ** t ** r m ** Eq {Nat} (S m) i)
def Vec = \(n : Nat) (t : *). IFix Nat (VecF t) n
def Nil : {t : *} -> Vec Z t = \{t}. IIn {Nat} {VecF t} {Z} (InL (refl {Nat} {Z}))
def Cons
  : {t : *} -> (n : Nat) -> t -> Vec n t -> Vec (S n) t
  = \{t} n hd tl. IIn {Nat} {VecF t} {S n} (InR {_} {{m : Nat} ** t ** Vec m t ** Eq {Nat} (S n) (S m)} ({n}, hd, tl, refl {Nat} {S n}))

def indVecR
  : {t : *}
    -> {P : (n : Nat) -> Vec n t -> *}
    -> (
      ({m : Nat} -> (y : Vec m t) -> P m y)
      -> {m : Nat}
      -> (z : VecF t (\(n : Nat). Vec n t) m)
      -> P m (IIn {Nat} {VecF t} {m} z)
    )
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} f {n} x. genindIFix {Nat} {VecF t} {P} f {n} x

-- def indVec
--  : {t : *}
--    -> {P : (n : Nat) -> Vec n t -> *}
--    -> P Z (Nil {t})
--    -> ({m : Nat} -> (hd : t) -> (tl : Vec m t) -> P m tl -> P (S m) (Cons {t} m hd tl))
--    -> {n : Nat}
--    -> (x : Vec n t)
--    -> P n x
--  = \{t} {P} nil cons {n} x. indVecR {t} {P} (\rec {k} z.
--    caseSum {Eq {Nat} Z k} {(m : Nat) ** t ** r m ** Eq {Nat} (S m) k} z
--      (\q. rewrite {Nat} {\m. P m (IIn {Nat} {VecF t} {m} (InL (refl {Nat} {m})))} q nil)
--      (\p. cons {p.0} p.1 p.2 (rec {p.0} p.2)))
--    {n} x

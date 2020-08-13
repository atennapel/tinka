import lib/unit.p

def BoolD = data UnitType
  (\_. (UnitType, \_ _ E. E ()))
  (\_. (UnitType, \_ _ E. E ()))
def Bool = tcon BoolD ()
def True : Bool = con 0 BoolD ()
def False : Bool = con 1 BoolD ()
def indBool
  : {P : Bool -> *}
    -> P True
    -> P False
    -> (b : Bool) -> P b
  = \{P} t f b. elim BoolD (\_. P) () b (\_. t) (\_. f)
def if
  : {t : *} -> Bool -> t -> t -> t
  = \{t} c a b. indBool {\_. t} a b c

def MaybeD = \t. data UnitType
  (\_. (UnitType, \_ _ E. E ()))
  (\_. (t, \_ _ E. E ()))
def Maybe = \t. tcon (MaybeD t) ()
def Nothing : {t : *} -> Maybe t = \{t}. con 0 (MaybeD t) ()
def Just : {t : *} -> t -> Maybe t = \{t} v. con 1 (MaybeD t) v
def indMaybe
  : {t : *}
    -> {P : Maybe t -> *}
    -> P Nothing
    -> ((y : t) -> P (Just y))
    -> (x : Maybe t) -> P x
  = \{t} {P} n j x. elim (MaybeD t) (\_. P) () x (\_. n) j
def caseMaybe
  : {t : *} -> {r : *} -> Maybe t -> r -> (t -> r) -> r
  = \{t} {r} m n j. indMaybe {t} {\_. r} n j m

def NatD = data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
def Nat = tcon NatD ()
def Z : Nat = con 0 NatD ()
def S : Nat -> Nat = \n. con 1 NatD n
def elimNat
  : {P : Nat -> *}
    -> P Z
    -> ((m : Nat) -> P (S m))
    -> (n : Nat) -> P n
  = \{P} z s n. elim NatD (\_. P) () n (\_. z) s
def caseNat
  : {t : *} -> Nat -> t -> (Nat -> t) -> t
  = \{t} n z s. elimNat {\_. t} z s n

def pred : Nat -> Nat = \n. caseNat n Z (\m. m)

def ListD = \t. data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (t ** R (), \_ _ E. E ()))
def List = \t. tcon (ListD t) ()
def Nil : {t : *} -> List t = \{t}. con 0 (ListD t) ()
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. con 1 (ListD t) (hd, tl)
def elimList
  : {t : *}
    -> {P : List t -> *}
    -> P Nil
    -> ((hd : t) -> (tl : List t) -> P (Cons hd tl))
    -> (l : List t) -> P l
  = \{t} {P} n c l. elim (ListD t) (\_. P) () l (\_. n) (\p. c p.fst p.snd)
def caseList
  : {t : *} -> {r : *} -> List t -> r -> (t -> List t -> r) -> r
  = \{t} {r} l n c. elimList {t} {\_. r} n c l

def VecD = \t. data Nat
  (\R. (UnitType, \_ _ E. E Z))
  (\R. ({n : Nat} ** t ** R n, \a _ E. E (S a.fst)))
def Vec : Nat -> * -> * = \n t. tcon (VecD t) n
def VNil : {t : *} -> Vec Z t = \{t}. con 0 (VecD t) ()
def VCons : {t : *} -> {n : Nat} -> t -> Vec n t -> Vec (S n) t = \{t} {n} hd tl. con 1 (VecD t) ({n}, hd, tl)
def elimVec
  : {t : *}
    -> {P : (n : Nat) -> Vec n t -> *}
    -> P Z VNil
    -> ({m : Nat} -> (hd : t) -> (tl : Vec m t) -> P (S m) (VCons hd tl))
    -> {n : Nat} -> (v : Vec n t) -> P n v
  = \{t} {P} n c {m} v. elim (VecD t) P m v (\_. n) (\p. c {p.fst} p.snd.fst p.snd.snd)
def caseVec
  : {n : Nat} -> {t : *} -> {r : *} -> Vec n t -> r -> ({m : Nat} -> t -> Vec m t -> r) -> r
  = \{n} {t} {r} v nil c. elimVec {t} {\_ _. r} nil c {n} v

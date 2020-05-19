import lib/ex.p

-- church-encoded natural numbers
def Nat = {t : *} -> t -> (t -> t) -> t
def Z : Nat = \z s. z
def S : Nat -> Nat = \n z s. s (n z s)

def add : Nat -> Nat -> Nat = \a b. a b S

-- induction using unsafeUnpack
def INat = \(n : Nat). {P : Nat -> *} -> P Z -> ({m : Nat} -> P m -> P (S m)) -> P n
def IZ : INat Z = \z s. z
def IS : {n : Nat} -> INat n -> INat (S n) = \{n} nn {P} z s. s {n} (nn {P} z s)

def nat2INat
  : Nat -> Ex Nat INat
  = \n. n {Ex Nat INat} (Pack {Nat} {INat} {Z} IZ) (\mm. unpack {Nat} {INat} {Ex Nat INat} mm \{k} kk. Pack {Nat} {INat} {S k} (IS {k} kk))

def indNat
  : {P : Nat -> *} -> P Z -> ({m : Nat} -> P m -> P (S m)) -> (n : Nat) -> P n
  = \{P} z s n. (unsafeUnpack {Nat} {INat} {n} (nat2INat n)) {P} z s

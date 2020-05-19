import lib/nat.p

def Vec = \(n : Nat) (t : *). {r : Nat -> *} -> r Z -> ({m : Nat} -> t -> r m -> r (S m)) -> r n
def VNil : {t : *} -> Vec Z t = \n c. n
def VCons
  : {n : Nat} -> {t : *} -> t -> Vec n t -> Vec (S n) t
  = \{n} {t} hd tl {r} nil cons. cons {n} hd (tl {r} nil cons)

-- induction
def IVec = \(n : Nat) (t : *) (x : Vec n t).
  {P : (n : Nat) -> Vec n t -> *}
  -> P Z (VNil {t})
  -> ({m : Nat} -> {l : Vec m t} -> (hd : t) -> (tl : P m l) -> P (S m) (VCons {m} {t} hd l))
  -> P n x
def IVNil
  : {t : *} -> IVec Z t (VNil {t})
  = \n c. n
def IVCons
  : {n : Nat} -> {t : *} -> {l : Vec n t} -> (hd : t) -> (tl : IVec n t l) -> IVec (S n) t (VCons {n} {t} hd l)
  = \hd tl {P} n c. c hd (tl {P} n c)

def vec2IVec
  : {n : Nat} -> {t : *} -> Vec n t -> Ex (Vec n t) (IVec n t)
  = \{n} {t} v. v {\n. Ex (Vec n t) (IVec n t)}
    (Pack {Vec Z t} {IVec Z t} {VNil {t}} (IVNil {t}))
    (\{m} hd tl.
      unpack {Vec m t} {IVec m t} {Ex (Vec (S m) t) (IVec (S m) t)} tl \{k} kk.
        Pack {Vec (S m) t} {IVec (S m) t} {VCons {m} {t} hd k} (IVCons {m} {t} {k} hd kk))

def indVec
  : {t : *} -> {P : (n : Nat) -> Vec n t -> *}
    -> P Z (VNil {t})
    -> ({m : Nat} -> {l : Vec m t} -> (hd : t) -> (tl : P m l) -> P (S m) (VCons {m} {t} hd l))
    -> {n : Nat}
    -> (x : Vec n t)
    -> P n x
  = \{t} {P} nil cons {n} x. (unsafeUnpack {Vec n t} {IVec n t} {x} (vec2IVec x)) {P} nil cons

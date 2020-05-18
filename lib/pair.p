import lib/ex.p

def Pair = \(a b : *). {t : *} -> (a -> b -> t) -> t
def MkPair
  : {a b : *} -> a -> b -> Pair a b
  = \x y f. f x y

def fst : {a b : *} -> Pair a b -> a = \p. p \x y. x
def snd : {a b : *} -> Pair a b -> b = \p. p \x y. y

-- induction
def IPair = \(a b : *) (p : Pair a b). {P : Pair a b -> *} -> ((x : a) -> (y : b) -> P (MkPair {a} {b} x y)) -> P p
def IMkPair
  : {a b : *} -> (x : a) -> (y : b) -> IPair a b (MkPair {a} {b} x y)
  = \x y f. f x y

def pair2IPair
  : {a b : *} -> (p : Pair a b) -> Ex (Pair a b) (IPair a b)
  = \{a} {b} p. p {Ex (Pair a b) (IPair a b)} (\x y. Pack {Pair a b} {IPair a b} {MkPair {a} {b} x y} (IMkPair {a} {b} x y))

def indPair
  : {a b : *} -> {P : Pair a b -> *} -> ((x : a) -> (y : b) -> P (MkPair {a} {b} x y)) -> (p : Pair a b) -> P p
  = \{a} {b} {P} f p. (unsafeUnpack {Pair a b} {IPair a b} {p} (pair2IPair p)) {P} f

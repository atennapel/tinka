def Pair = \(a b : *). data P. a -> b -> P
def MkPair
  : {a b : *} -> a -> b -> Pair a b
  = \{a b} x y. con {Pair a b} 0 1 x y

def indPair
  : {a b : *} -> {P : Pair a b -> *} -> ((x : a) -> (y : b) -> P (MkPair x y)) -> (p : Pair a b) -> P p
  = \{a b} {P} pp p. case {Pair a b} {P} p (\_. pp)

def casePair
  : {a b : *} -> {r : *} -> (a -> b -> r) -> Pair a b -> r
  = \{a b} {r} f p. indPair {a} {b} {\_. r} f p

def fst
  : {a b : *} -> Pair a b -> a
  = \p. casePair (\x y. x) p

def snd
  : {a b : *} -> Pair a b -> b
  = \p. casePair (\x y. y) p

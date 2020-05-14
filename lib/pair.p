def Pair = \(a b : *). {t : *} -> (a -> b -> t) -> t
def MkPair
  : {a b : *} -> a -> b -> Pair a b
  = \x y f. f x y

def fst : {a b : *} -> Pair a b -> a = \p. p \x y. x
def snd : {a b : *} -> Pair a b -> b = \p. p \x y. y

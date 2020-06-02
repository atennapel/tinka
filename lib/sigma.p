import lib/eq.p

def Sigma = \(a : *) (b : a -> *). (x : a) ** b x

def indSigma
  : {a : *} -> {b : a -> *} -> {P : Sigma a b -> *} -> ((x : a) -> (y : b x) -> P (x, y)) -> (s : Sigma a b) -> P s
  = \{a} {b} {P} f s. f (fst s) (snd s)

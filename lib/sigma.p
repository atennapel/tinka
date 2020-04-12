def Sigma = \(a : *) (b : a -> *). {t : *} -> ((x : a) -> b x -> t) -> t
def MkSigma : {a : *} -> {b : a -> *} -> (x : a) -> b x -> Sigma a b
  = \x y f. f x y

def fstS : {a : *} -> {b : a -> *} -> Sigma a b -> a = \p. p \x y. x

def indSigma
  : {a : *} -> {b : a -> *} -> {P : Sigma a b -> *} -> ((x : a) -> (y : b x) -> P (MkSigma x y)) -> (x : Sigma a b) -> P x
  = \{a b} {P} p x. induction x {P} p

def sndS : {a : *} -> {b : a -> *} -> (x : Sigma a b) -> b (fstS x)
  = \{a b} x. indSigma {a} {b} {\x. b (fstS x)} (\x y. y) x

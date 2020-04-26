def Sigma = \(a : *) (b : a -> *). data S. (x : a) -> b x -> S
def MkSigma
  : {a : *} -> {b : a -> *} -> (x : a) -> b x -> Sigma a b
  = \{a} {b} x y. con {Sigma a b} 0 1 x y

def indSigma
  : {a : *} -> {b : a -> *} -> {P : Sigma a b -> *} -> ((x : a) -> (y : b x) -> P (MkSigma x y)) -> (s : Sigma a b) -> P s
  = \{a b} {P} p s. case {Sigma a b} {P} s (\_. p)

def caseSigma
  : {a : *} -> {b : a -> *} -> {t : *} -> ((x : a) -> b x -> t) -> Sigma a b -> t
  = \{a b} {t} p s. indSigma {a} {b} {\_. t} p s

def fstS
  : {a : *} -> {b : a -> *} -> Sigma a b -> a
  = \p. caseSigma (\x y. x) p

def sndS
  : {a : *} -> {b : a -> *} -> (s : Sigma a b) -> b (fstS s)
  = \{a} {b} s. indSigma {a} {b} {\s. b (fstS s)} (\x y. y) s

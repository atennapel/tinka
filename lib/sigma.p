import lib/ex.p

def Sigma = \(a : *) (b : a -> *). {t : *} -> ((x : a) -> b x -> t) -> t
def MkSigma
  : {a : *} -> {b : a -> *} -> (x : a) -> b x -> Sigma a b
  = \x y f. f x y

def ISigma = \(a : *) (b : a -> *) (s : Sigma a b). {P : Sigma a b -> *} -> ((x : a) -> (y : b x) -> P (MkSigma {a} {b} x y)) -> P s
def IMkSigma
  : {a : *} -> {b : a -> *} -> (x : a) -> (y : b x) -> ISigma a b (MkSigma {a} {b} x y)
  = \x y f. f x y

def sigma2ISigma
  : {a : *} -> {b : a -> *} -> Sigma a b -> Ex (Sigma a b) (ISigma a b)
  = \{a} {b} s. s {Ex (Sigma a b) (ISigma a b)} (\x y. Pack {Sigma a b} {ISigma a b} {MkSigma {a} {b} x y} (IMkSigma {a} {b} x y))

def indSigma
  : {a : *} -> {b : a -> *} -> {P : Sigma a b -> *} -> ((x : a) -> (y : b x) -> P (MkSigma {a} {b} x y)) -> (s : Sigma a b) -> P s
  = \{a} {b} {P} f s. (unsafeUnpack {Sigma a b} {ISigma a b} {s} (sigma2ISigma s)) {P} f

def fst : {a : *} -> {b : a -> *} -> Sigma a b -> a = \{a} {b} s. s {a} (\x y. x)
def snd : {a : *} -> {b : a -> *} -> (s : Sigma a b) -> b (fst s) = \{a} {b} s. indSigma {a} {b} {\s. b (fst s)} (\x y. y) s

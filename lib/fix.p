-- mendler-style inductive types
def Alg = \(f : * -> *) (t : *). {r : *} -> (r -> t) -> f r -> t
def Fix = \(f : * -> *). {t : *} -> Alg f t -> t

def fold
  : {f : * -> *} -> {t : *} -> Alg f t -> Fix f -> t
  = \alg fix. fix alg

def In
  : {f : * -> *} -> f (Fix f) -> Fix f
  = \x alg. alg (fold alg) x

def out
  : {f : * -> *} -> Fix f -> f (Fix f)
  = \{f} x. x {f (Fix f)} (\_ y. unsafeCast y)

def gindFix
  : {f : * -> *} -> {P : Fix f -> *} -> (((x : Fix f) -> P x) -> (y : f (Fix f)) -> P (In {f} y)) -> (x : Fix f) -> P x
  = \{f} {P} alg x. x {P x} (unsafeCast alg)

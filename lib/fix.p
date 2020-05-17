-- mendler-style inductive types
def Alg = \(f : * -> *) (t : *). Ex * \r. (r -> t) -> f r -> t
def Fix = \(f : * -> *). {t : *} -> Alg f t -> t

def fold
  : {f : * -> *} -> {t : *} -> Alg f t -> Fix f -> t
  = \alg fix. fix alg

def In
  : {f : * -> *} -> f (Fix f) -> Fix f
  = \{f} x {t} alg. (unsafeUnpack {*} {\r. (r -> t) -> f r -> t} {Fix f} alg) (fold alg) x

def out
  : {f : * -> *} -> Fix f -> f (Fix f)
  = \{f} x. x {f (Fix f)} (pack {*} {\r. (r -> f (Fix f)) -> f r -> f (Fix f)} {Fix f} (\_ y. y))

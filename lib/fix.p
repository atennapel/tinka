import lib/functor.p

-- mendler-style inductive types
def Alg = \(f : * -> *) (t : *). {r : *} -> (r -> t) -> f r -> t
def Fix = \(f : * -> *). {t : *} -> Alg f t -> t

def fold
  : {f : * -> *} -> {t : *} -> Alg f t -> Fix f -> t
  = \alg fix. fix alg

def In
  : {f : * -> *} -> f (Fix f) -> Fix f
  = \x alg. alg (fold alg) x

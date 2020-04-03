def Fix = \(f : * -> *). fix (r : *). {x : *} -> ((r -> x) -> f r -> x) -> x

def fold : {f : * -> *} -> {x : *} -> ((Fix f -> x) -> f (Fix f) -> x) -> Fix f -> x
  = \{f x} alg r. unroll r {x} alg
def In : {f : * -> *} -> f (Fix f) -> Fix f
  = \x. roll \{t} alg. alg (fold {_} {t} alg) x

def caseFix : {f : * -> *} -> Fix f -> f (Fix f)
  = \{f} x. fold {f} {f (Fix f)} (\_ x. x) x

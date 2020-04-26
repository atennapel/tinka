def Fix = \(f : * -> *). data r. ({x : *} -> ((r -> x) -> f r -> x) -> x) -> r

def InF : {f : * -> *} -> ({x : *} -> ((Fix f -> x) -> f (Fix f) -> x) -> x) -> Fix f = \{f} x. con {Fix f} 0 1 x
def OutF : {f : * -> *} -> Fix f -> ({x : *} -> ((Fix f -> x) -> f (Fix f) -> x) -> x) =
  \{f} x. case {Fix f} {\_. ({x : *} -> ((Fix f -> x) -> f (Fix f) -> x) -> x)} x (\_ y. y)

def fold : {f : * -> *} -> {x : *} -> ((Fix f -> x) -> f (Fix f) -> x) -> Fix f -> x
  = \{f x} alg r. OutF r {x} alg
def In : {f : * -> *} -> f (Fix f) -> Fix f
  = \{f} x. InF {f} \{t} alg. alg (fold {_} {t} alg) x

def caseFix : {f : * -> *} -> Fix f -> f (Fix f)
  = \{f} x. fold {f} {f (Fix f)} (\_ x. x) x

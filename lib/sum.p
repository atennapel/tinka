def Sum = \(a b : *). {t : *} -> (a -> t) -> (b -> t) -> t
def L : {a b : *} -> a -> Sum a b = \x f g. f x
def R : {a b : *} -> b -> Sum a b = \x f g. g x

def indSum
  : {a b : *} -> {P : Sum a b -> *} -> ((x : a) -> P (L x)) -> ((x : b) -> P (R x)) -> (x : Sum a b) -> P x
  = \{a b} {P} pl pr x. induction x {P} pl pr

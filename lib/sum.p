import lib/ex.p

def Sum = \(a b : *). {t : *} -> (a -> t) -> (b -> t) -> t
def InL : {a b : *} -> a -> Sum a b = \x f g. f x
def InR : {a b : *} -> b -> Sum a b = \x f g. g x

-- induction
def ISum = \(a b : *) (s : Sum a b). {P : Sum a b -> *} -> ((x : a) -> P (InL {a} {b} x)) -> ((x : b) -> P (InR {a} {b} x)) -> P s
def IInL : {a b : *} -> (x : a) -> ISum a b (InL {a} {b} x) = \x f g. f x
def IInR : {a b : *} -> (x : b) -> ISum a b (InR {a} {b} x) = \x f g. g x

def sum2ISum
  : {a b : *} -> Sum a b -> Ex (Sum a b) (ISum a b)
  = \{a} {b} s. s {Ex (Sum a b) (ISum a b)}
      (\x. Pack {Sum a b} {ISum a b} {InL {a} {b} x} (IInL {a} {b} x))
      (\x. Pack {Sum a b} {ISum a b} {InR {a} {b} x} (IInR {a} {b} x))

def indSum
  : {a b : *} -> {P : Sum a b -> *} -> ((x : a) -> P (InL {a} {b} x)) -> ((x : b) -> P (InR {a} {b} x)) -> (s : Sum a b) -> P s
  = \{a} {b} {P} f g s. (unsafeUnpack {Sum a b} {ISum a b} {s} (sum2ISum s)) {P} f g

def Sum = \(a b : *). data S. a -> S | b -> S
def Inl
  : {a b : *} -> a -> Sum a b
  = \{a b} x. con {Sum a b} 0 2 x
def Inr
  : {a b : *} -> b -> Sum a b
  = \{a b} x. con {Sum a b} 1 2 x

def indSum
  : {a b : *} -> {P : Sum a b -> *} -> ((x : a) -> P (Inl x)) -> ((x : b) -> P (Inr x)) -> (x : Sum a b) -> P x
  = \{a b} {P} l r x. case {Sum a b} {P} x (\_. l) (\_. r)

def caseSum
  : {a b : *} -> {t : *} -> (a -> t) -> (b -> t) -> Sum a b -> t
  = \{a b} {t} l r x. indSum {a} {b} {\_. t} l r x

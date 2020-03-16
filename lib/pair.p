def Pair = \(a b : *). {t : *} -> (a -> b -> t) -> t
def P : {a b : *} -> a -> b -> Pair a b = \x y f. f x y

def fst : {a b : *} -> Pair a b -> a = \{a} {b} p. p {a} \x y. x
def snd : {a b : *} -> Pair a b -> b = \{a} {b} p. p {b} \x y. y

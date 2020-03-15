def Sum = \(a b : *). {t : *} -> (a -> t) -> (b -> t) -> t
def L : {a b : *} -> a -> Sum a b = \x {t} f g. f x
def R : {a b : *} -> b -> Sum a b = \x {t} f g. g x

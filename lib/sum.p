def Sum = \(a b : *). {t : *} -> (a -> t) -> (b -> t) -> t
def InL : {a b : *} -> a -> Sum a b = \x f g. f x
def InR : {a b : *} -> b -> Sum a b = \x f g. g x

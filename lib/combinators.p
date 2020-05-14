def id : {t : *} -> t -> t = \x. x
def const : {a b : *} -> a -> b -> a = \x y. x
def compose : {a b c : *} -> (b -> c) -> (a -> b) -> a -> c = \f g x. f (g x)

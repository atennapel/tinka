def Nat = {N@t : *} -> t -> (N -> t -> t) -> t
def Z : Nat = \z s. z
def S : Nat -> Nat = \n z s. s n (n z s)

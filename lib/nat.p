-- church-encoded natural numbers
def Nat = {t : *} -> t -> (t -> t) -> t
def Z : Nat = \z s. z
def S : Nat -> Nat = \n z s. s (n z s)

def add : Nat -> Nat -> Nat = \a b. a b S

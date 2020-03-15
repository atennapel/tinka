-- church nats
def Nat = {t : *} -> t -> (t -> t) -> t
def Z : Nat = \z s. z
def S : Nat -> Nat = \n {t} z s. s (n {t} z s)

def add : Nat -> Nat -> Nat = \a b. a {Nat} b S

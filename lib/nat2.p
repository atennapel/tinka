import lib/fix2.p
import lib/maybe.p

def Nat = Fix MaybeD
def Z : Nat = In {MaybeD} (True, ())
def S : Nat -> Nat = \n. In {MaybeD} (False, (n, ()))

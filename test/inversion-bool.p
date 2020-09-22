import lib/bool.p
import lib/nat.p
import lib/nat.extra.p

def TYPE = Bool
def BOOL : TYPE = True
def NAT : TYPE = False

def decode : TYPE -> * = \t. if t Bool Nat

def eqTYPE : (t : TYPE) -> decode t -> decode t -> Bool = \t. indBool {\t. decode t -> decode t -> Bool} eqBool eqNat t

def test1 = eqTYPE BOOL True False
def test2 = eqTYPE NAT 1 2
def test3 = eqTYPE _ True False

import lib/sum.p
import lib/bool.p
import lib/nat.p
import lib/nat.extra.p
import lib/unit.p

def TYPE = Sum UnitType UnitType
def BOOL : TYPE = InL ()
def NAT : TYPE = InR ()

def decode : TYPE -> * = \t. caseSum t (\_. Bool) (\_. Nat)

def eqTYPE
  : (t : TYPE) -> decode t -> decode t -> Bool
  = \t. indSum {_} {_} {\t. decode t -> decode t -> Bool} (\_. eqBool) (\_. eqNat) t

def test1 = eqTYPE BOOL True False
def test2 = eqTYPE NAT 1 2
def test3 = eqTYPE _ True False

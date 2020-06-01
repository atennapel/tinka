import lib/unit.p
import lib/sum.p
import lib/fix.p

def NatF = \(r : *). Sum UnitType r
def Nat = Fix NatF
def Z : Nat = In {NatF} (InL Unit)
def S : Nat -> Nat = \n. In {NatF} (InR n)

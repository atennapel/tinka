import lib/unit.p
import lib/nat.p
import lib/bool.p
import lib/list.p

def Showable = List Nat

def Show = \t. t -> Showable
def show : {t : *} -> Show t -> t -> Showable = \x. x

def showNatUnary : Show Nat = \n. cataNat n (Nil {Nat}) (Cons 49)
def showUnit : Show UnitType = \_. Cons 40 (Cons 41 Nil)
def showBool : Show Bool =
  \b. if b (Cons 84 (Cons 114 (Cons 117 (Cons 101 Nil)))) (Cons 70 (Cons 97 (Cons 108 (Cons 115 (Cons 101 Nil)))))

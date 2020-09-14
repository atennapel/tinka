import lib/unit.p
import lib/nat.p
import lib/bool.p
import lib/list.p

def Codepoint = Nat
def String = List Codepoint

def Showable = String

def Show = \t. t -> Showable
def show : {t : *} -> Show t -> t -> Showable = \x. x

def showString : Show String = \s. s
def showNatUnary : Show Nat = \n. cataNat n (Nil {Nat}) (Cons 49)
def showUnit : Show UnitType = \_. "()"
def showBool : Show Bool = \b. if b "True" "False"

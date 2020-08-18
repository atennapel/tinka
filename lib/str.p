import lib/nat.p
import lib/list.p

def Str = List Nat

def Show = \t. t -> Str
def show : {t : *} -> Show t -> t -> Str = \x. x

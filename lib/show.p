import lib/nat.p
import lib/list.p

def Showable = List Nat

def Show = \t. t -> Showable
def show : {t : *} -> Show t -> t -> Showable = \x. x

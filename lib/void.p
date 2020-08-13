import lib/unit.p

def VoidD = data UnitType
def Void = tcon VoidD ()

def indVoid
  : {P : Void -> *} -> (x : Void) -> P x
  = \{P} x. elim VoidD (\_. P) () x

def caseVoid
  : {t : *} -> Void -> t
  = \{t} x. indVoid {\_. t} x

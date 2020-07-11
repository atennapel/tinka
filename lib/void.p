import lib/nat.p
import lib/fin.p

def Void = Fin Z

def indVoid
  : {P : Void -> *} -> (x : Void) -> P x
  = %elimFin0

def caseVoid
  : {t : *} -> Void -> t
  = \{t} x. indVoid {\_. t} x

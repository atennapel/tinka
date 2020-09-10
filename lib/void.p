import lib/fin.p

def Void = Fin 0

def indVoid
  : {P : Void -> *} -> (x : Void) -> P x
  = \{P} x. caseNFin {0} x {P}

def caseVoid
  : {t : *} -> Void -> t
  = \{t} x. indVoid {\_. t} x

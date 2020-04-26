def Void = data V.

def indVoid
  : {P : Void -> *} -> (v : Void) -> P v
  = \{P} v. case {Void} {P} v

def caseVoid
  : {t : *} -> Void -> t
  = \{t} v. indVoid {\_. t} v

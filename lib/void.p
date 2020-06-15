def Void = %Void

def indVoid
  : {P : Void -> *} -> (x : Void) -> P x
  = %indVoid

def caseVoid
  : {t : *} -> Void -> t
  = \{t} x. indVoid {\_. t} x

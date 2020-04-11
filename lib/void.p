def Void = {t : *} -> t

def indVoid
  : {P : Void -> *} -> (x : Void) -> P x
  = \{P} v. v {P v}

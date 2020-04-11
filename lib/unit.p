def UnitType = {t : *} -> t -> t
def Unit : UnitType = \x. x

def indUnit
  : {P : UnitType -> *} -> P Unit -> (x : UnitType) -> P x
  = \{P} pu x. induction x {P} pu

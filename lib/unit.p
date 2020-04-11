import lib/eq.p

def UnitType = {t : *} -> t -> t
def Unit : UnitType = \x. x

def indUnit
  : {P : UnitType -> *} -> P Unit -> (x : UnitType) -> P x
  = \{P} pu x. induction x {P} pu

def uniqUnit
  : (x : UnitType) -> Eq UnitType x Unit
  = \x. indUnit {\x. Eq UnitType x Unit} (refl {UnitType} {Unit}) x

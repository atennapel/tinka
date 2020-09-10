import lib/fin.p

def UnitType = Fin 1
def Unit : UnitType = 0

def indUnitE
  : {P : UnitType -> *} -> P Unit -> {u : UnitType} -> P u
  = \{P} p {u}. p

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \p _. p

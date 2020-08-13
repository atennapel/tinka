def UnitType = %UnitType
def Unit : UnitType = %Unit

def indUnitE
  : {P : UnitType -> *} -> P Unit -> {u : UnitType} -> P u
  = \{P} p {u}. p

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \p _. p

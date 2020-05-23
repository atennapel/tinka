def UnitType = #1
def Unit : UnitType = @0

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \{P} pu u. ?1 {P} u pu

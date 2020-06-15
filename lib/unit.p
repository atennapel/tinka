import lib/eq.p

def UnitType = %UnitType
def Unit : UnitType = %Unit

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = %indUnit

def uniteta
  : {x : UnitType} -> Eq {UnitType} x Unit
  = \{x}. Refl {UnitType} {x}

def unitetaR
  : {x : UnitType} -> Eq {UnitType} Unit x
  = \{x}. symm (uniteta {x})

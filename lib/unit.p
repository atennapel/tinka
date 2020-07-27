import lib/eq.p

def UnitType = %UnitType
def Unit : UnitType = %Unit

def indUnitE
  : {P : UnitType -> *} -> P Unit -> {u : UnitType} -> P u
  = \{P} p {u}. p

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \p _. p

def uniteta
  : {x : UnitType} -> Eq {UnitType} x Unit
  = \{x}. Refl {UnitType} {x}

def unitetaR
  : {x : UnitType} -> Eq {UnitType} Unit x
  = \{x}. symm (uniteta {x})

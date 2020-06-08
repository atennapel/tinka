import lib/eq.p

def UnitType = #1
def Unit : UnitType = @0

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \{P} pu u. ?1 {P} u pu

def uniteta
  : {x : UnitType} -> Eq {UnitType} x Unit
  = \{x}. refl {UnitType} {x}

def unitetaR
  : {x : UnitType} -> Eq {UnitType} Unit x
  = \{x}. symm (uniteta {x})

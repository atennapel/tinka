import lib/eq.p

def UnitType = #1
def Unit : UnitType = @0

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \{P} pu u. ?1 {P} u pu

def uniqUnit
  : (x : UnitType) -> Eq UnitType x Unit
  = \x. indUnit {\x. Eq UnitType x Unit} (refl {UnitType} {Unit}) x

def uniqUnitR
  : (x : UnitType) -> Eq UnitType Unit x
  = \x. symm (uniqUnit x)

def uniqUnitE
  : {x : UnitType} -> Eq UnitType x Unit
  = %uniqUnit

def uniqUnitER
  : {x : UnitType} -> Eq UnitType Unit x
  = \{x}. symm (uniqUnitE {x})

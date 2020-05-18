import lib/ex.p

-- church-encoded unit type
def UnitType = {t : *} -> t -> t
def Unit : UnitType = \x. x

-- induction using unsafeUnpack
def IUnitType = \(u : UnitType). {P : UnitType -> *} -> P Unit -> P u
def IUnit : IUnitType Unit = \x. x

def unit2IUnit
  : (u : UnitType) -> Ex UnitType IUnitType
  = \u. u {Ex UnitType IUnitType} (pack {UnitType} {IUnitType} {Unit} IUnit)

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \{P} pu u. (unsafeUnpack {UnitType} {IUnitType} {u} (unit2IUnit u)) {P} pu

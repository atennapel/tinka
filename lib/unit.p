import lib/eq.p

def UnitType = data U. U
def Unit : UnitType = con {UnitType} 0 1

def indUnit
  : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  = \{P} pu u. case {UnitType} {P} u (\_. pu)

def caseUnit
  : {t : *} -> t -> UnitType -> t
  = \{t} x _. x

def unitUniq
  : (u : UnitType) -> Eq UnitType u Unit
  = \u. indUnit {\u. Eq UnitType u Unit} (refl {UnitType} {Unit}) u

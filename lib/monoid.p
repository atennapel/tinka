import lib/unit.p

def Monoid = \t. (unit : t) ** (append : t -> t -> t) ** UnitType
def mkMonoid
  : {t : *} -> t -> (t -> t -> t) -> Monoid t
  = \unit append. (unit, append, ())

def unit : {t : *} -> Monoid t -> t = \m. m.unit
def append : {t : *} -> Monoid t -> t -> t -> t = \m. m.append

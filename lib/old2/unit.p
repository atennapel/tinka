import lib/eq.p

def UnitType = {t : *} -> t -> t
def Unit : UnitType = \x. x

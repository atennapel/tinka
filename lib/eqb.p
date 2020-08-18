import lib/bool.p

def Eqb = \t. t -> t -> Bool
def eqb : {t : *} -> Eqb t -> t -> t -> Bool = \x. x

def eqbBool : Eqb Bool = eqBool

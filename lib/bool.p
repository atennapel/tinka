def Bool = {t : *} -> t -> t -> t
def True : Bool = \t f. t
def False : Bool = \t f. f

def if : {t : *} -> Bool -> t -> t -> t = \{t} b. b {t}

def indBool
  : {P : Bool -> *} -> P True -> P False -> (x : Bool) -> P x
  = \{P} pt pf b. induction b {P} pt pf

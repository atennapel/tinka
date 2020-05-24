def End : Desc = condesc End
def Rec : Desc -> Desc = \d. condesc Rec d
def Arg : {t : *} -> (t -> Desc) -> Desc = \{t} f. condesc Arg t f

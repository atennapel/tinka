def PrimNat = {t : *} -> t -> (t -> t) -> t
def PrimNatZ : PrimNat = \z s. z
def PrimNatS : PrimNat -> PrimNat = \n z s. s (n z s)

def PrimChar = PrimNat

def PrimStr = {t : *} -> t -> (PrimChar -> t -> t) -> t
def PrimStrNil : PrimStr = \n c. n
def PrimStrCons : PrimChar -> PrimStr -> PrimStr = \hd tl n c. c hd (tl n c)

import lib/unit.p
import lib/bool.p
import lib/fix.p

def ListD : * -> Desc = \t. Arg {Bool} \b. if b End (Arg {t} \_. Rec End)
def List : * -> * = \t. Fix (ListD t)
def Nil : {t : *} -> List t = \{t}. In {ListD t} (@0, ())
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. In {ListD t} (@1, hd, tl, ())

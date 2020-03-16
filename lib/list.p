import lib/unit.p
import lib/sum.p
import lib/pair.p
import lib/fix.p

def ListF = \(t r : *). {x : *} -> x -> (t -> r -> x) -> x
def List = \(t : *). Fix (ListF t)
def Nil : {t : *} -> List t = \{t}. In {ListF t} \n c. n
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. In {ListF t} \n c. c hd tl

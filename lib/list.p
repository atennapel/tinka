import lib/unit.p
import lib/sum.p
import lib/fix.p

def ListF = \(t r : *). Sum UnitType (t ** r)
def List = \(t : *). Fix (ListF t)
def Nil : {t : *} -> List t = \{t}. In {ListF t} (InL ())
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. In {ListF t} (InR (hd, tl))

def caseList
  : {t r : *} -> List t -> r -> (t -> List t -> r) -> r
  = \l n c. caseSum (outFix l) (\_. n) (\p. c p.fst p.snd)

def cataList
  : {t r : *} -> List t -> r -> (t -> r -> r) -> r
  = \{t} {r} l n c. mendlerFix {ListF t} {r} (\rec y. caseSum y (\_. n) (\p. c p.fst (rec p.snd))) l

def paraList
  : {t r : *} -> List t -> r -> (t -> List t -> r -> r) -> r
  = \{t} {r} l n c. genrecFix {ListF t} {r} (\rec y. caseSum y (\_. n) (\p. let tl = p.snd in c p.fst tl (rec tl))) l

def indList
  : {t : *}
    -> {P : List t -> *}
    -> P Nil
    -> ({tl : List t} -> (hd : t) -> P tl -> P (Cons hd tl))
    -> (l : List t)
    -> P l
  = \{t} {P} n c l. genindFix {ListF t} {P}
    (\rec y. indSum {UnitType} {t ** List t} {\s. P (In {ListF t} s)}
      (\_. n)
      (\p. let tl = .snd p in c {tl} p.fst (rec tl))
      y)
    l

def map
  : {a b : *} -> (a -> b) -> List a -> List b
  = \{a} {b} f l. cataList l (Nil {b}) (\hd tl. Cons (f hd) tl)

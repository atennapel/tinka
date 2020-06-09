import lib/unit.p
import lib/sum.p
import lib/fix.p
import lib/maybe.p

def ListF = \(t r : *). Sum UnitType (t ** r)
def List = \(t : *). Fix (ListF t)
def Nil : {t : *} -> List t = \{t}. In {ListF t} (InL ())
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. In {ListF t} (InR (hd, tl))

def genindList
  : {t : *}
    -> {P : List t -> *}
    -> P Nil
    -> (((l : List t) -> P l) -> (hd : t) -> (tl : List t) -> P (Cons hd tl))
    -> (l : List t)
    -> P l
  = \{t} {P} n c l. genindFix {ListF t} {P}
    (\rec y. indSum {UnitType} {t ** List t} {\s. P (In {ListF t} s)}
      (\_. n)
      (\p. c rec p.fst p.snd)
      y)
    l

def indList
  : {t : *}
    -> {P : List t -> *}
    -> P Nil
    -> ({tl : List t} -> (hd : t) -> P tl -> P (Cons hd tl))
    -> (l : List t)
    -> P l
  = \{t} {P} n c l. genindList {t} {P} n (\rec hd tl. c {tl} hd (rec tl)) l

def dcaseList
  : {t : *} -> {P : List t -> *} -> (l : List t) -> P Nil -> ((hd : t) -> (tl : List t) -> P (Cons hd tl)) -> P l
  = \{t} {P} l n c. genindList {t} {P} n (\_. c) l

def recList
  : {t r : *} -> List t -> r -> ((List t -> r) -> t -> List t -> r) -> r
  = \{t} {r} l n c. genindList {t} {\_. r} n c l

def caseList
  : {t r : *} -> List t -> r -> (t -> List t -> r) -> r
  = \l n c. recList l n (\rec hd tl. c hd tl)

def cataList
  : {t r : *} -> List t -> r -> (t -> r -> r) -> r
  = \l n c. recList l n (\rec hd tl. c hd (rec tl))

def paraList
  : {t r : *} -> List t -> r -> (t -> List t -> r -> r) -> r
  = \l n c. recList l n (\rec hd tl. c hd tl (rec tl))

def map
  : {a b : *} -> (a -> b) -> List a -> List b
  = \{a} {b} f l. cataList l (Nil {b}) (\hd tl. Cons (f hd) tl)

def head
  : {t : *} -> List t -> Maybe t
  = \{t} l. caseList l (Nothing {t}) (\hd _. Just hd)

def tail
  : {t : *} -> List t -> Maybe (List t)
  = \{t} l. caseList l (Nothing {List t}) (\_ tl. Just tl)

import lib/unit.p
import lib/maybe.p
import lib/rec.p

def ListD = \t. data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (t ** R (), \_ _ E. E ()))
def List = \t. tcon (ListD t) ()
def Nil : {t : *} -> List t = \{t}. con 0 (ListD t) ()
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. con 1 (ListD t) (hd, tl)

def dcaseList
  : {t : *}
    -> {P : List t -> *}
    -> (l : List t)
    -> P Nil
    -> ((hd : t) -> (tl : List t) -> P (Cons hd tl))
    -> P l
  = \{t} {P} l n c. elim (ListD t) (\_. P) () l (\_. n) (\p. c p.fst p.snd)
def caseList
  : {t r : *} -> List t -> r -> (t -> List t -> r) -> r
  = \{t} {r} l n c. dcaseList {t} {\_. r} l n c

def genindList
  : {t : *}
    -> {P : List t -> *}
    -> P Nil
    -> (((l : List t) -> P l) -> (hd : t) -> (tl : List t) -> P (Cons hd tl))
    -> (l : List t)
    -> P l
  = \{t} {P} n c. drec {List t} {P} \rec l. dcaseList {t} {P} l n (\hd tl. c rec hd tl)

def indList
  : {t : *}
    -> {P : List t -> *}
    -> P Nil
    -> ({tl : List t} -> (hd : t) -> P tl -> P (Cons hd tl))
    -> (l : List t)
    -> P l
  = \{t} {P} n c l. genindList {t} {P} n (\rec hd tl. c {tl} hd (rec tl)) l

def recList
  : {t r : *} -> List t -> r -> ((List t -> r) -> t -> List t -> r) -> r
  = \{t} {r} l n c. genindList {t} {\_. r} n c l

def cataList
  : {t r : *} -> List t -> r -> (t -> r -> r) -> r
  = \l n c. recList l n (\rec hd tl. c hd (rec tl))

def paraList
  : {t r : *} -> List t -> r -> (t -> List t -> r -> r) -> r
  = \l n c. recList l n (\rec hd tl. c hd tl (rec tl))

def mapList
  : {a b : *} -> (a -> b) -> List a -> List b
  = \{a} {b} f l. cataList l (Nil {b}) (\hd tl. Cons (f hd) tl)

def headList
  : {t : *} -> List t -> Maybe t
  = \{t} l. caseList l (Nothing {t}) (\hd _. Just hd)

def tailList
  : {t : *} -> List t -> Maybe (List t)
  = \{t} l. caseList l (Nothing {List t}) (\_ tl. Just tl)

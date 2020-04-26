import lib/prim.p
import lib/functor.p
import lib/nat.p

def List = \(t : *). data L. L | t -> L -> L
def Nil : {t : *} -> List t = \{t}. con {List t} 0 2
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. con {List t} 1 2 hd tl

def indList
  : {t : *} -> {P : List t -> *} -> P Nil -> ((hd : t) -> (tl : List t) -> P tl -> P (Cons hd tl)) -> (l : List t) -> P l
  = \{t} {P} n c l. case {List t} {P} l (\_. n) (\rec h k. c h k (rec k))

def caseList
  : {t : *} -> {r : *} -> r -> (t -> List t -> r) -> List t -> r
  = \{t} {r} n c l. case {List t} {\_. r} l (\_. n) (\_ hd tl. c hd tl)

def foldList : {t r : *} -> List t -> r -> (t -> r -> r) -> r
  = \{t} {r} l n c. indList {t} {\_. r} n (\hd _ tlr. c hd tlr) l

def mapList : {a b : *} -> (a -> b) -> List a -> List b
  = \{a b} f l. foldList {a} {List b} l (Nil {b}) (\hd r. Cons {b} (f hd) r)

def functorList : Functor List = mapList

def toPrimStr : List Nat -> PrimStr = \l. foldList (mapList toPrimChar l) PrimStrNil PrimStrCons 

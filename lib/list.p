import lib/unit.p
import lib/sum.p
import lib/pair.p
import lib/fix.p
import lib/functor.p

import lib/prim.p
import lib/nat.p

def ListF = \(t : *) (r : *). {x : *} -> x -> (t -> r -> x) -> x
def List = \(t : *). Fix (ListF t)
def Nil : {t : *} -> List t = \{t}. In {ListF t} \{x} n c. n
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. In {ListF t} \{x} n c. c hd tl

def caseList : {t r : *} -> List t -> r -> (t -> List t -> r) -> r
  = \{t} l n c. caseFix {ListF t} l n c
def recList : {t r : *} -> List t -> r -> ((List t -> r) -> t -> List t -> r) -> r
  = \{t} {r} l n c. fold {ListF t} {r} (\rec case. case {r} n (\hd tl. c rec hd tl)) l

def foldList : {t r : *} -> List t -> r -> (t -> r -> r) -> r
  = \{t} l n c. recList {t} l n (\rec hd tl. c hd (rec tl))

def mapList : {a b : *} -> (a -> b) -> List a -> List b
  = \{a b} f l. foldList {a} {List b} l (Nil {b}) (\hd r. Cons {b} (f hd) r)

def functorList : Functor List = mapList

def toPrimStr : List Nat -> PrimStr = \l. foldList (mapList toPrimChar l) PrimStrNil PrimStrCons 

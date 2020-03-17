import lib/unit.p
import lib/sum.p
import lib/pair.p
import lib/fix.p
import lib/functor.p

def ListF = \(t r : *). {x : *} -> x -> (t -> r -> x) -> x
def List = \(t : *). Fix (ListF t)
def Nil : {t : *} -> List t = \{t}. In {ListF t} \n c. n
def Cons : {t : *} -> t -> List t -> List t = \{t} hd tl. In {ListF t} \n c. c hd tl

def foldList
  : {t r : *} -> List t -> r -> (t -> r -> r) -> r
  = \{t} l n c. fold {ListF t} (\rc k. k n (\hd tl. c hd (rc tl))) l

def mapList
  : {a b : *} -> (a -> b) -> List a -> List b
  = \{a} {b} fn l. foldList {a} {List b} l Nil (\hd tl. Cons (fn hd) tl)

def functorList : Functor List = mapList

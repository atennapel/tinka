import lib/unit.p
import lib/bool.p
import lib/ifix.p
import lib/eq.p

def genindType
  : {P : * -> *}
    -> (((t : *) -> P t) -> P *)
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) -> B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ({x : A} -> B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) ** B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ({x : A} ** B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) ** {B x}))
    -> (((t : *) -> P t) -> P UnitType)
    -> (((t : *) -> P t) -> P Bool)
    -> (((t : *) -> P t) -> (I : *) -> (F : (I -> *) -> (I -> *)) -> (i : I) -> P (IFix I F i))
    -> (((t : *) -> P t) -> (A : *) -> (B : *) -> (a : A) -> (b : B) -> P (HEq {A} {B} a b))
    -> (t : *) -> P t
  = %genindType

def dcaseType
  : {P : * -> *}
    -> P *
    -> ((A : *) -> (B : A -> *) -> P ((x : A) -> B x))
    -> ((A : *) -> (B : A -> *) -> P ({x : A} -> B x))
    -> ((A : *) -> (B : A -> *) -> P ((x : A) ** B x))
    -> ((A : *) -> (B : A -> *) -> P ({x : A} ** B x))
    -> ((A : *) -> (B : A -> *) -> P ((x : A) ** {B x}))
    -> P UnitType
    -> P Bool
    -> ((I : *) -> (F : (I -> *) -> (I -> *)) -> (i : I) -> P (IFix I F i))
    -> ((A : *) -> (B : *) -> (a : A) -> (b : B) -> P (HEq {A} {B} a b))
    -> (t : *) -> P t
  = \{P} pt pp1 pp2 ps1 ps2 ps3 pu pb pf pe x. genindType {P} (\_. pt) (\_. pp1) (\_. pp2) (\_. ps1) (\_. ps2) (\_. ps3) (\_. pu) (\_. pb) (\_. pf) (\_. pe) x

def recType
  : {t : *}
    -> *
    -> ((* -> t) -> t)
    -> ((* -> t) -> (A : *) -> (A -> *) -> t)
    -> ((* -> t) -> (A : *) -> (A -> *) -> t)
    -> ((* -> t) -> (A : *) -> (A -> *) -> t)
    -> ((* -> t) -> (A : *) -> (A -> *) -> t)
    -> ((* -> t) -> (A : *) -> (A -> *) -> t)
    -> ((* -> t) -> t)
    -> ((* -> t) -> t)
    -> ((* -> t) -> (I : *) -> ((I -> *) -> (I -> *)) -> (i : I) -> t)
    -> ((* -> t) -> (A : *) -> (B : *) -> A -> B -> t)
    -> t
  = \{t} x pt pp1 pp2 ps1 ps2 ps3 pu pb pf pe. genindType {\_. t} pt pp1 pp2 ps1 ps2 ps3 pu pb pf pe x

def caseType
  : {t : *}
    -> *
    -> t
    -> ((A : *) -> (A -> *) -> t)
    -> ((A : *) -> (A -> *) -> t)
    -> ((A : *) -> (A -> *) -> t)
    -> ((A : *) -> (A -> *) -> t)
    -> ((A : *) -> (A -> *) -> t)
    -> t
    -> t
    -> ((I : *) -> ((I -> *) -> (I -> *)) -> (i : I) -> t)
    -> ((A : *) -> (B : *) -> A -> B -> t)
    -> t
  = \{t} x pt pp1 pp2 ps1 ps2 ps3 pu pb pf pe. recType {t} x (\_. pt) (\_. pp1) (\_. pp2) (\_. ps1) (\_. ps2) (\_. ps3) (\_. pu) (\_. pb) (\_. pf) (\_. pe)

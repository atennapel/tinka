import lib/eq.p
import lib/unit.p
import lib/void.p

def Bool = %Bool
def True : Bool = %True
def False : Bool = %False

def indBool
  : {P : Bool -> *}
    -> P True
    -> P False
    -> (b : Bool) -> P b
  = %indBool

def if
  : {t : *} -> Bool -> t -> t -> t
  = \{t} c a b. indBool {\_. t} a b c

def not : Bool -> Bool = \b. if b False True
def and : Bool -> Bool -> Bool = \a b. if a b False
def or : Bool -> Bool -> Bool = \a b. if a True b

def eqBool : Bool -> Bool -> Bool = \a b. if a b (not b)
def neqBool : Bool -> Bool -> Bool = \a b. not (eqBool a b)
def xor = neqBool

def liftBool : Bool -> * = \b. if b UnitType Void

def trueNeqFalse
  : Neq {Bool} True False
  = \eq. rewrite {Bool} {liftBool} eq (Unit : liftBool True)

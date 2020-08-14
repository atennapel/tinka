import lib/eq.p
import lib/unit.p
import lib/void.p

def BoolD = data UnitType
  (\_. (UnitType, \_ _ E. E ()))
  (\_. (UnitType, \_ _ E. E ()))
def Bool = tcon BoolD ()
def True : Bool = con 0 {BoolD} ()
def False : Bool = con 1 {BoolD} ()

def indBool
  : {P : Bool -> *}
    -> P True
    -> P False
    -> (b : Bool) -> P b
  = \{P} t f b. elim {BoolD} {\_. P} {()} b (\_ _. t) (\_ _. f)

def if
  : {t : *} -> Bool -> t -> t -> t
  = \{t} c a b. indBool {\_. t} a b c

def liftBool : Bool -> * = \b. if b UnitType Void

def trueNeqFalse
  : Neq {Bool} True False
  = \eq. rewrite {Bool} {liftBool} eq (Unit : liftBool True)

def not : Bool -> Bool = \b. if b False True
def and : Bool -> Bool -> Bool = \a b. if a b False
def or : Bool -> Bool -> Bool = \a b. if a True b

def eqBool : Bool -> Bool -> Bool = \a b. if a b (not b)

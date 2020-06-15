import lib/eq.p
import lib/unit.p
import lib/void.p

def Bool = %Bool
def True : Bool = %True
def False : Bool = %False

def indBool
  : {P : Bool -> *} -> P True -> P False -> (b : Bool) -> P b
  = %indBool

def if
  : {r : *} -> Bool -> r -> r -> r
  = \{r} b t f. indBool {\_. r} t f b

def liftBool : Bool -> * = \b. if b UnitType Void

def trueNeqFalse
  : Neq {Bool} True False
  = \eq. rewrite {Bool} {liftBool} eq (Unit : liftBool True)

def not : Bool -> Bool = \b. if b False True
def and : Bool -> Bool -> Bool = \a b. if a b False
def or : Bool -> Bool -> Bool = \a b. if a True b

def eqBool : Bool -> Bool -> Bool = \a b. if a b (not b)

import lib/eq.p
import lib/unit.p
import lib/void.p

def Bool = #2
def True : Bool = @0
def False : Bool = @1

def indBool
  : {P : Bool -> *} -> P True -> P False -> (b : Bool) -> P b
  = \{P} t f b. ?2 {P} b t f

def if
  : {r : *} -> Bool -> r -> r -> r
  = \{r} b t f. indBool {\_. r} t f b

def liftBool : (b : Bool) -> * = \b. if b UnitType Void

def trueNeqFalse
  : Neq {Bool} True False
  = \eq. rewrite {Bool} {liftBool} eq (Unit : liftBool True)

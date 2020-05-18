import lib/eq.p
import lib/unit.p
import lib/void.p

def Bool = {t : *} -> t -> t -> t
def True : Bool = \t f. t
def False : Bool = \t f. f

def if
  : {r : *} -> Bool -> r -> r -> r
  = \{r} b t f. b {r} t f

def liftBool : (b : Bool) -> * = \b. if b UnitType Void

def trueNeqFalse
  : Neq Bool True False
  = \eq. castF {Bool} {True} {False} {liftBool} eq (Unit : liftBool True)

-- induction
def IBool = \(b : Bool). {P : Bool -> *} -> P True -> P False -> P b
def ITrue : IBool True = \t f. t
def IFalse : IBool False = \t f. f

def bool2IBool
  : (b : Bool) -> Ex Bool IBool
  = \b. b {Ex Bool IBool} (Pack {Bool} {IBool} {True} ITrue) (Pack {Bool} {IBool} {False} IFalse)

def indBool
  : {P : Bool -> *} -> P True -> P False -> (b : Bool) -> P b
  = \{P} t f b. (unsafeUnpack {Bool} {IBool} {b} (bool2IBool b)) {P} t f

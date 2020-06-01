import lib/ifix.p
import lib/unit.p

import lib/unsafecast.p

def fToIndexed : (* -> *) -> ((UnitType -> *) -> (UnitType -> *)) = \f r _. f (r ())

def Fix : (* -> *) -> * = \f. IFix UnitType (fToIndexed f) ()
def In : {f : * -> *} -> f (Fix f) -> Fix f = \{f} x. IIn {UnitType} {fToIndexed f} {()} x 

def propToIndexed
  : {F : * -> *} -> (Fix F -> *) -> ((i : UnitType) -> IFix UnitType (fToIndexed F) i -> *)
  = \{F} P u x. P (rewrite {UnitType} {\i. IFix UnitType (fToIndexed F) i} (uniqUnit u) x)

def genindFix
  : {F : * -> *} -> {P : Fix F -> *} -> (((y : Fix F) -> P y) -> (z : F (Fix F)) -> P (In {F} z)) -> (x : Fix F) -> P x
  = \{F} {P} f x.
    genindIFix {UnitType} {fToIndexed F} {propToIndexed P}
      -- (\rec {i} z. rewrite {UnitType} {\i. propToIndexed {F} P i (IIn {UnitType} {fToIndexed F} {i} z)} (uniqUnitR i) (f (rec {()}) z))
      (\rec {i} z. unsafeCast (f (rec {()}) z))
      {()}
      x

def outFix : {f : * -> *} -> Fix f -> f (Fix f) = \{f} x. genindFix {f} {\_. f (Fix f)} (\_ z. z) x

def genrecFix
  : {F : * -> *} -> {t : *} -> ((Fix F -> t) -> F (Fix F) -> t) -> Fix F -> t
  = \{F} {t}. genindFix {F} {\_. t}

def mendlerFix
  : {F : * -> *} -> {t : *} -> ({r : *} -> (r -> t) -> F r -> t) -> Fix F -> t
  = \{F} {t} alg x. genrecFix {F} {t} (alg {Fix F}) x

import lib/unit.p
import lib/functor.p

def MaybeD = \t. data UnitType
  (\_. (UnitType, \_ _ E. E ()))
  (\_. (t, \_ _ E. E ()))
def Maybe = \t. tcon (MaybeD t) ()
def Nothing : {t : *} -> Maybe t = \{t}. con 0 {MaybeD t} ()
def Just : {t : *} -> t -> Maybe t = \{t} v. con 1 {MaybeD t} v

def indMaybe
  : {t : *}
    -> {P : Maybe t -> *}
    -> P Nothing
    -> ((y : t) -> P (Just y))
    -> (x : Maybe t) -> P x
  = \{t} {P} n j x. elim {MaybeD t} {\_. P} {()} x (\_ _. n) (\_. j)

def caseMaybe
  : {t r : *} -> Maybe t -> r -> (t -> r) -> r
  = \{t} {r} m n j. indMaybe {t} {\_. r} n j m

def mapMaybe
  : {a b : *} -> (a -> b) -> Maybe a -> Maybe b
  = \{a} {b} f m. caseMaybe m (Nothing {b}) (\x. Just (f x))

def functorMaybe : Functor Maybe = mapMaybe

import lib/unit.p
import lib/sum.p
import lib/eq.p

def Maybe = \(t : *). Sum UnitType t
def Nothing : {t : *} -> Maybe t = \{t}. InL ()
def Just : {t : *} -> t -> Maybe t = \{t} x. InR x

def caseMaybe
  : {t r : *} -> Maybe t -> r -> (t -> r) -> r
  = \{t} {r} m n j. caseSum m (\_. n) j

def indMaybe
  : {t : *} -> {P : Maybe t -> *} -> P (Nothing {t}) -> ((x : t) -> P (Just {t} x)) -> (m : Maybe t) -> P m
  = \{t} {P} n j m. indSum {UnitType} {t} {P} (\u. rewrite {UnitType} {\u. P (InL u)} (uniqUnitR u) n) j m

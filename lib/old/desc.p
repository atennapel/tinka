import lib/unit.p

def Desc : * = %Desc
def End : Desc = %End
def Rec : Desc -> Desc = \d. %Rec d
def Arg : {t : *} -> (t -> Desc) -> Desc = \{t} f. %Arg {t} f

def indDesc
  : {P : Desc -> *}
    -> P End
    -> ((r : Desc) -> P r -> P (Rec r))
    -> ({t : *} -> (f : t -> Desc) -> ((x : t) -> P (f x)) -> P (Arg {t} f))
    -> (d : Desc)
    -> P d
  = \{P} e r a d. %indDesc d {P} e r a

def interpDesc : Desc -> * -> *
  = \d. indDesc {\_. * -> *}
    (\_. UnitType)
    (\r pr x. x ** pr x)
    (\{t} f pf x. (s : t) ** pf s x)
    d

def genMap
  : (d : Desc) -> {a : *} -> {b : *} -> (a -> b) -> interpDesc d a -> interpDesc d b
  = \d. indDesc {\d. {a : *} -> {b : *} -> (a -> b) -> interpDesc d a -> interpDesc d b}
    (\{a} {b} f x. x)
    (\r pr {a} {b} f x. (f (fst x), pr {a} {b} f (snd x)))
    (\{t} f pf {a} {b} fn x. (fst x, pf (fst x) {a} {b} fn (snd x)))
    d

def CasesDesc
  : (d : Desc) -> * -> * -> *
  = \d. indDesc {\d. * -> * -> *}
    (\a b. b)
    (\_ r a b. a -> r a b)
    (\{t} _ pf a b. (x : t) -> pf x a b)
    d

def genCase
  : (d : Desc) -> {a b : *} -> interpDesc d a -> CasesDesc d a b -> b
  = \d. indDesc {\d. {a b : *} -> interpDesc d a -> CasesDesc d a b -> b}
    (\{a} {b} x c. c)
    (\r pr {a} {b} x c. pr {a} {b} (snd x) (c (fst x)))
    (\{t} f pf {a} {b} x c. pf (fst x) {a} {b} (snd x) (c (fst x)))
    d

import lib/unit.p

def End : Desc = condesc End
def Rec : Desc -> Desc = \d. condesc Rec d
def Arg : {t : *} -> (t -> Desc) -> Desc = \{t} f. condesc Arg t f

def indDesc
  : {P : Desc -> *}
    -> P End
    -> ((r : Desc) -> P r -> P (Rec r))
    -> ({t : *} -> (f : t -> Desc) -> ((x : t) -> P (f x)) -> P (Arg {t} f))
    -> (d : Desc)
    -> P d
  = \{P} e r a d. inddesc d P e r a

def interpDesc : Desc -> * -> *
  = \d. indDesc {\_. * -> *}
    (\_. UnitType)
    (\r pr x. x ** pr x)
    (\{t} f pf x. (s : t) ** pf s x)
    d

def AllDesc
  : (d : Desc) -> (x : *) -> (P : x -> *) -> interpDesc d x -> *
  = \d. indDesc {\d. (x : *) -> (P : x -> *) -> interpDesc d x -> *}
    (\x P xs. UnitType)
    (\r pr x P xs. (P (fst xs)) ** (pr x P (snd xs)))
    (\{t} f pf x P xs. pf (fst xs) x P (snd xs))
    d

def allDesc
  : (d : Desc) -> {x : *} -> {P : x -> *} -> (p : (y : x) -> P y) -> (xs : interpDesc d x) -> AllDesc d x P xs
  = \d. indDesc {\d. {x : *} -> {P : x -> *} -> (p : (y : x) -> P y) -> (xs : interpDesc d x) -> AllDesc d x P xs}
    (\{x} {P} p xs. xs)
    (\r pr {x} {P} p xs. (p (fst xs), pr {x} {P} p (snd xs)))
    (\{t} f pf {x} {P} p xs. pf (fst xs) {x} {P} p (snd xs))
    d

def genMap
  : (d : Desc) -> {a : *} -> {b : *} -> (a -> b) -> interpDesc d a -> interpDesc d b
  = \d. indDesc {\d. {a : *} -> {b : *} -> (a -> b) -> interpDesc d a -> interpDesc d b}
    (\{a} {b} f x. x)
    (\r pr {a} {b} f x. (f (fst x), pr {a} {b} f (snd x)))
    (\{t} f pf {a} {b} fn x. (fst x, pf (fst x) {a} {b} fn (snd x)))
    d

import lib/desc.p

def Fix : Desc -> * = %Fix
def In : {d : Desc} -> interpDesc d (Fix d) -> Fix d = %In

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

def indFix
  : (D : Desc) -> (x : Fix D) -> {P : Fix D -> *} -> ((d : interpDesc D (Fix D)) -> AllDesc D (Fix D) P d -> P (In {D} d)) -> P x
  = %indFix

def dcaseFix
  : (D : Desc) -> (x : Fix D) -> {P : Fix D -> *} -> ((d : interpDesc D (Fix D)) -> P (In {D} d)) -> P x
  = \D x {P} f. indFix D x {P} (\a b. f a)

def caseFix
  : (D : Desc) -> (x : Fix D) -> {t : *} -> (interpDesc D (Fix D) -> t) -> t
  = \D x {t} f. dcaseFix D x {\_. t} f

def out
  : (D : Desc) -> Fix D -> interpDesc D (Fix D)
  = \D x. indFix D x {\_. interpDesc D (Fix D)} (\y _. y)

def replaceCataFix
  : (D : Desc) -> {X Y : *} -> (xs : interpDesc D X) -> AllDesc D X (\_. Y) xs -> interpDesc D Y
  = \D. indDesc {\D. {X Y : *} -> (xs : interpDesc D X) -> AllDesc D X (\_. Y) xs -> interpDesc D Y}
    (\{X} {Y} xs ys. ())
    (\r pr {X} {Y} xs ys. (fst ys, pr {X} {Y} (snd xs) (snd ys)))
    (\{t} f pf {X} {Y} xs ys. (fst xs, pf (fst xs) {X} {Y} (snd xs) ys))
    D

def cataFix
  : (D : Desc) -> {t : *} -> (interpDesc D t -> t) -> Fix D -> t
  = \D {t} f x. indFix D x {\_. t} \xs hs. f (replaceCataFix D {Fix D} {t} xs hs)

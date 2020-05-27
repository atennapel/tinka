def Ex = \(t : *) (f : t -> *). {r : *} -> ({x : t} -> f x -> r) -> r

def Pack
  : {t : *} -> {f : t -> *} -> {x : t} -> f x -> Ex t f
  = \x f. f x

def unpack
  : {t : *} -> {f : t -> *} -> {r : *} -> Ex t f -> ({x : t} -> f x -> r) -> r
  = \x f. x f

def unsafeUnpack
  : {t : *} -> {f : t -> *} -> {x : t} -> Ex t f -> f x
  = \{t} {f} {x} e. e \f. unsafeCast f

-- induction
def IEx = \(t : *) (f : t -> *) (e : Ex t f). {P : Ex t f -> *} -> ({x : t} -> (y : f x) -> P (Pack {t} {f} {x} y)) -> P e
def IPack
  : {t : *} -> {f : t -> *} -> {x : t} -> (y : f x) -> IEx t f (Pack {t} {f} {x} y)
  = \x f. f x

def ex2IEx
  : {t : *} -> {f : t -> *} -> Ex t f -> Ex (Ex t f) (IEx t f)
  = \{a} {b} e. e {Ex (Ex a b) (IEx a b)} (\{x} y. Pack {Ex a b} {IEx a b} {Pack {a} {b} {x} y} (IPack {a} {b} {x} y))

def indEx
  : {t : *} -> {f : t -> *} -> {P : Ex t f -> *} -> ({x : t} -> (y : f x) -> P (Pack {t} {f} {x} y)) -> (e : Ex t f) -> P e
  = \{t} {f} {P} fn e. (unsafeUnpack {Ex t f} {IEx t f} {e} (ex2IEx e)) {P} fn

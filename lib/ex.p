def Ex = \(t : *) (f : t -> *). {r : *} -> ({x : t} -> f x -> r) -> r

def pack
  : {t : *} -> {f : t -> *} -> {x : t} -> f x -> Ex t f
  = \x f. f x

def unpack
  : {t : *} -> {f : t -> *} -> {r : *} -> Ex t f -> ({x : t} -> f x -> r) -> r
  = \x f. x f

def unsafeUnpack
  : {t : *} -> {f : t -> *} -> {x : t} -> Ex t f -> f x
  = \{t} {f} {x} e. e \f. unsafeCast f

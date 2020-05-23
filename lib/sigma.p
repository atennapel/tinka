def indSigma
  : {a : *} -> {b : a -> *} -> {P : ((x : a) ** b x) -> *} -> ((x : a) -> (y : b x) -> P (x, y)) -> (s : (x : a) ** b x) -> P s
  = \{a} {b} {P} f s. f (fst s) (snd s)

def drec
  : {a : *} -> {b : a -> *} -> (((x : a) -> b x) -> ((x : a) -> b x)) -> (x : a) -> b x
  = %drec
def rec
  : {a : *} -> {b : *} -> ((a -> b) -> (a -> b)) -> a -> b
  = \{a} {b}. drec {a} {\_. b}
def dreci
  : {a : *} -> {b : a -> *} -> (({x : a} -> b x) -> ({x : a} -> b x)) -> {x : a} -> b x
  = %dreci
def reci
  : {a : *} -> {b : *} -> (({a} -> b) -> ({a} -> b)) -> {a} -> b
  = \{a} {b}. dreci {a} {\_. b}

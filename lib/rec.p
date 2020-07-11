def drec
  : {a : *} -> {b : a -> *} -> (((x : a) -> b x) -> (x : a) -> b x) -> (x : a) -> b x
  = %drec

def dreci
  : {a : *} -> {b : a -> *} -> (({x : a} -> b x) -> {x : a} -> b x) -> {x : a} -> b x
  = %dreci

def rec
  : {a : *} -> {b : *} -> ((a -> b) -> a -> b) -> a -> b
  = \{a} {b} f. drec {a} {\_. b} f

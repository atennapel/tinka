def Fix = \(f : * -> *). data r. f r -> r

def In : {f : * -> *} -> f (Fix f) -> Fix f = \{f} x. con {Fix f} 0 1 x
def Out : {f : * -> *} -> Fix f -> f (Fix f) = \{f} x. case {Fix f} {\_. f (Fix f)} x (\y. y)

def dcaseFix
  : {f : * -> *} -> {P : Fix f -> *} -> (x : Fix f) -> ((c : f (Fix f)) -> P (In {f} c)) -> P x
  = \{f} {P} x c. case {Fix f} {P} x c

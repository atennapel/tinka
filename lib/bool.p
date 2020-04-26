def Bool = data B. B | B
def True : Bool = con {Bool} 0 2
def False : Bool = con {Bool} 1 2

def indBool
  : {P : Bool -> *} -> P True -> P False -> (b : Bool) -> P b
  = \{P} t f b. case {Bool} {P} b (\_. t) (\_. f)

def caseBool
  : {r : *} -> r -> r -> Bool -> r
  = \{r} t f b. indBool {\_. r} t f b

def if
  : {r : *} -> Bool -> r -> r -> r
  = \{r} b t f. caseBool {r} t f b

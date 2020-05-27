import lib/desc.p

def Fix : Desc -> * = %Fix
def In : {d : Desc} -> interpDesc d (Fix d) -> Fix d = %In

def indFix
  : (D : Desc) -> (x : Fix D) -> {P : Fix D -> *} -> ((d : interpDesc D (Fix D)) -> AllDesc D (Fix D) P d -> P (In {D} d)) -> P x
  = %indFix

def out
  : (D : Desc) -> Fix D -> interpDesc D (Fix D)
  = \D x. indFix D x {\_. interpDesc D (Fix D)} (\y _. y)

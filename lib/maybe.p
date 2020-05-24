import lib/unit.p
import lib/bool.p
import lib/desc.p

def MaybeD = Arg {Bool} \b. if b End (Rec End)
def Maybe = interpDesc MaybeD

def Nothing : {t : *} -> Maybe t = \{t}. (True, ())
def Just : {t : *} -> t -> Maybe t = \{t} x. (False, (x, ()))

def mapMaybe : {a : *} -> {b : *} -> (a -> b) -> Maybe a -> Maybe b = genMap MaybeD

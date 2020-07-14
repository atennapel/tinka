def SigmaD = \(A : *) (B : A -> *). data * (\S. (x : A) -> B x -> S)
def Sigma = \(A : *) (B : A -> *). tcon (SigmaD A B)
def MkSigma : {A : *} -> {B : A -> *} -> (x : A) -> B x -> Sigma A B = \{A} {B} x y. con 0 (SigmaD A B) x y

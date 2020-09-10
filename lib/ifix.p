def IFix = %IFix
def IIn
  : {I : *} -> {F : (I -> *) -> (I -> *)} -> {i : I} -> F (IFix I F) i -> IFix I F i
  = %IIn
def genindIFix
  : {I : *}
    -> {F : (I -> *) -> (I -> *)}
    -> {P : (i : I) -> IFix I F i -> *}
    -> (
      ({i : I} -> (y : IFix I F i) -> P i y)
      -> {i : I}
      -> (z : F (IFix I F) i)
      -> P i (IIn {I} {F} {i} z)
    )
    -> {i : I}
    -> (x : IFix I F i)
    -> P i x
  = %genindIFix

def genrecIFix
  : {I : *}
    -> {F : (I -> *) -> (I -> *)}
    -> {t : *}
    -> (
      ({i : I} -> IFix I F i -> t)
      -> {i : I}
      -> F (IFix I F) i
      -> t
    )
    -> {i : I}
    -> IFix I F i
    -> t
  = \{I} {F} {t} f {i} x. genindIFix {I} {F} {\_ _. t} f {i} x

def outIFix
  : {I : *} -> {F : (I -> *) -> (I -> *)} -> {i : I} -> IFix I F i -> F (IFix I F) i
  = \{I} {F} {i} x. genindIFix {I} {F} {\i _. F (IFix I F) i} (\_ {_} z. z) {i} x

import lib/rec.p

def IFix : (I : *) -> ((I -> *) -> I -> *) -> I -> * = %IFix
def IIn
  : {I : *} -> {F : (I -> *) -> I -> *} -> {i : I} -> F (IFix I F) i -> IFix I F i
  = %IIn
def elimIFix
  : {I : *} -> {F : (I -> *) -> I -> *}
    -> {P : (i : I) -> IFix I F i -> *}
    -> ({i : I} -> (z : F (IFix I F) i) -> P i (IIn {I} {F} {i} z))
    -> {i : I} -> (x : IFix I F i) -> P i x
  = %elimIFix

def outIFix
  : {I : *} -> {F : (I -> *) -> (I -> *)} -> {i : I} -> IFix I F i -> F (IFix I F) i
  = \{I} {F} {i} x. elimIFix {I} {F} {\i _. F (IFix I F) i} (\{_} z. z) {i} x

def genindIFix
  : {I : *} -> {F : (I -> *) -> I -> *}
    -> {P : (i : I) -> IFix I F i -> *}
    -> (({i : I} -> (y : IFix I F i) -> P i y) -> {i : I} -> (z : F (IFix I F) i) -> P i (IIn {I} {F} {i} z))
    -> {i : I} -> (x : IFix I F i) -> P i x
  = \{I} {F} {P} r. dreci {I} {\i. (x : IFix I F i) -> P i x} \rec {i} x. elimIFix {I} {F} {P} (\{i} z. r rec {i} z) {i} x 

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

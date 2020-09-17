import lib/void.p
import lib/eq.p

def unsafeElimHEq
  : {A : *}
    -> {a : A}
    -> {P : (b : A) -> HEq {A} {A} a b -> *}
    -> P a (HRefl {A} {a})
    -> {b : A}
    -> {p : HEq {A} {A} a b}
    -> P b p
  = %unsafeElimHEq

def unsafeElimEq
  : {A : *}
    -> {a : A}
    -> {P : (b : A) -> Eq a b -> *}
    -> P a (Refl {A} {a})
    -> {b : A}
    -> {p : Eq {A} a b}
    -> P b p
  = unsafeElimHEq

def unsafeRewrite
  : {t : *} -> {f : t -> *} -> {a b : t} -> {p : Eq {t} a b} -> f a -> f b
  = \{t} {f} {a} {b} {p} x. unsafeElimEq {t} {a} {\_ _. f b} x {b} {p}

def unsafeCast
  : {a b : *} -> {p : Eq a b} -> a -> b
  = \{a} {b} {p} x. unsafeRewrite {*} {\x. x} {a} {b} {p} x

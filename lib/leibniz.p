import lib/void.p
import lib/unsafecast.p

def Eq = \{t : *} (a b : t). {f : t -> *} -> f a -> f b
def Neq = \{t : *} (a b : t). Eq {t} a b -> Void

def castF
  : {t : *} -> {a b : t} -> {f : t -> *} -> (e : Eq {t} a b) -> f a -> f b
  = \{t} {a b} {f} e. e {f}

def cast
  : {a b : *} -> Eq {*} a b -> a -> b
  = \{a b}. castF {*} {a} {b} {\x. x}

def rewrite
  : {t : *} -> {f : t -> *} -> {a b : t} -> (e : Eq {t} a b) -> f a -> f b
  = \{t} {f} {a} {b} e. e {f}

def refl : {t : *} -> {x : t} -> Eq {t} x x = \x. x

def symm
  : {t : *} -> {a b : t} -> Eq {t} a b -> Eq {t} b a
  = \{t} {a b} x {f} fa. castF {t} {a} {b} {\x. f x -> f a} x (\x. x) fa

def lift
  : {t1 : *} -> {t2 : *} -> {a b : t1} -> {f : t1 -> t2} -> Eq {t1} a b -> Eq {t2} (f a) (f b)
  = \{t1} {t2} {a} {b} {f} e. e {\x. Eq {t2} (f a) (f x)} (refl {t2} {f a}) 

def dfuneta
  : {a : *} -> {b : a -> *} -> {f g : (x : a) -> b x} -> Eq {(x : a) -> b x} f g -> Eq {(x : a) -> b x} (\x. f x) (\x. g x)
  = \e. e

def dfunetaR
  : {a : *} -> {b : a -> *} -> {f g : (x : a) -> b x} -> Eq {(x : a) -> b x} (\x. f x) (\x. g x) -> Eq {(x : a) -> b x} f g
  = \e. e

def funeta
  : {a b : *} -> {f g : a -> b} -> Eq {a -> b} f g -> Eq {a -> b} (\x. f x) (\x. g x)
  = \e. e

def funetaR
  : {a b : *} -> {f g : a -> b} -> Eq {a -> b} (\x. f x) (\x. g x) -> Eq {a -> b} f g
  = \e. e

def dfunextR
  : {a : *} -> {b : a -> *} -> {f g : (x : a) -> b x} -> Eq {(x : a) -> b x} f g -> (x : a) -> Eq {b x} (f x) (g x)
  = \{a} {b} {f} {g} e x. lift {(x : a) -> b x} {b x} {f} {g} {\f. f x} e

def funextR
  : {a b : *} -> {f g : a -> b} -> Eq {a -> b} f g -> (x : a) -> Eq {b} (f x) (g x)
  = \{a} {b}. dfunextR {a} {\_. b}

def unsafeDFunext
  : {a : *} -> {b : a -> *} -> {f g : (x : a) -> b x} -> ((x : a) -> Eq {b x} (f x) (g x)) -> Eq {(x : a) -> b x} f g
  = \{a} {b} {f} {g} app. unsafeCast (refl {(x : a) -> b x} {f})

def unsafeFunext
  : {a b : *} -> {f g : a -> b} -> ((x : a) -> Eq {b} (f x) (g x)) -> Eq {a -> b} f g
  = \{a} {b}. unsafeDFunext {a} {\_. b}

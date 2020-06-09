import lib/unit.p
import lib/sum.p
import lib/fix.p

def BinF = \(r : *). Sum UnitType (Sum r r)
def Bin = Fix BinF
def BE : Bin = In {BinF} (InL ())
def B0 : Bin -> Bin = \n. In {BinF} (InR (InL n))
def B1 : Bin -> Bin = \n. In {BinF} (InR (InR n))

def genindBin
  : {P : Bin -> *}
    -> P BE
    -> (((m : Bin) -> P m) -> (m : Bin) -> P (B0 m))
    -> (((m : Bin) -> P m) -> (m : Bin) -> P (B1 m))
    -> (n : Bin)
    -> P n
  = \{P} be b0 b1 n. genindFix {BinF} {P}
    (\rec y. indSum {UnitType} {Sum Bin Bin} {\s. P (In {BinF} s)} (\_. be) (\z. indSum {Bin} {Bin} {\s. P (In {BinF} (InR s))} (\m. b0 rec m) (\m. b1 rec m) z) y)
    n

def indBin
  : {P : Bin -> *}
    -> P BE
    -> ({m : Bin} -> P m -> P (B0 m))
    -> ({m : Bin} -> P m -> P (B1 m))
    -> (n : Bin)
    -> P n
  = \{P} be b0 b1 n. genindBin {P} be (\rec m. b0 {m} (rec m)) (\rec m. b1 {m} (rec m)) n

def dcaseBin
  : {P : Bin -> *}
    -> P BE
    -> ((m : Bin) -> P (B0 m))
    -> ((m : Bin) -> P (B1 m))
    -> (n : Bin)
    -> P n
  = \{P} be b0 b1 n. genindBin {P} be (\_. b0) (\_. b1) n

def recBin
  : {t : *} -> Bin -> t -> ((Bin -> t) -> Bin -> t) -> ((Bin -> t) -> Bin -> t) -> t
  = \{t} b be b0 b1. genindBin {\_. t} be b0 b1 b

def caseBin
  : {t : *} -> Bin -> t -> (Bin -> t) -> (Bin -> t) -> t
  = \b be b0 b1. recBin b be (\_. b0) (\_. b1)

def cataBin
  : {t : *} -> Bin -> t -> (t -> t) -> (t -> t) -> t
  = \b be b0 b1. recBin b be (\rec m. b0 (rec m)) (\rec m. b1 (rec m))

def paraBin
  : {t : *} -> Bin -> t -> (Bin -> t -> t) -> (Bin -> t -> t) -> t
  = \b be b0 b1. recBin b be (\rec m. b0 m (rec m)) (\rec m. b1 m (rec m))

def zerob : Bin = BE
def incb : Bin -> Bin =
  \b. paraBin b
    (B1 BE)
    (\b _. B1 b)
    (\_ r. B0 r)

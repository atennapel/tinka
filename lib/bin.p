import lib/unit.p
import lib/sum.p
import lib/fix.p

def BinF = \(r : *). Sum UnitType (Sum r r)
def Bin = Fix BinF
def BE : Bin = In {BinF} (InL ())
def B0 : Bin -> Bin = \n. In {BinF} (InR (InL n))
def B1 : Bin -> Bin = \n. In {BinF} (InR (InR n))

def caseBin
  : {t : *} -> Bin -> t -> (Bin -> t) -> (Bin -> t) -> t
  = \b e b0 b1. caseSum (outFix b) (\_. e) (\s. caseSum s b0 b1)

def cataBin
  : {t : *} -> Bin -> t -> (t -> t) -> (t -> t) -> t
  = \{t} b e b0 b1. mendlerFix {BinF} {t} (\rec y.
      caseSum y (\_. e) (\z. caseSum z (\b. b0 (rec b)) (\b. b1 (rec b)))) b

def paraBin
  : {t : *} -> Bin -> t -> (Bin -> t -> t) -> (Bin -> t -> t) -> t
  = \{t} b e b0 b1. genrecFix {BinF} {t} (\rec y.
      caseSum y (\_. e) (\z. caseSum z (\b. b0 b (rec b)) (\b. b1 b (rec b)))) b

def BinZ : Bin = BE
def BinS : Bin -> Bin =
  \b. paraBin b
    (B1 BE)
    (\b _. B1 b)
    (\_ r. B0 r)

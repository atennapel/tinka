import lib/unit.p

def BinD = data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
def Bin = tcon BinD ()
def BE : Bin = con 0 {BinD} ()
def B0 : Bin -> Bin = \n. con 1 {BinD} n
def B1 : Bin -> Bin = \n. con 2 {BinD} n

def genindBin
  : {P : Bin -> *}
    -> P BE
    -> (((m : Bin) -> P m) -> (m : Bin) -> P (B0 m))
    -> (((m : Bin) -> P m) -> (m : Bin) -> P (B1 m))
    -> (n : Bin)
    -> P n
  = \{P} be b0 b1 n. elim {BinD} {\_. P} {()} n (\_ _. be) (\rec m. b0 (rec {()}) m) (\rec m. b1 (rec {()}) m)

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

import lib/unit.p

def BinD = data UnitType
  (\R. (UnitType, \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
  (\R. (R (), \_ _ E. E ()))
def Bin = tcon BinD ()
def BE : Bin = con 0 {BinD} ()
def B0 : Bin -> Bin = \n. con 1 {BinD} n
def B1 : Bin -> Bin = \n. con 2 {BinD} n

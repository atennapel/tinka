import lib/unit.p
import lib/fix.p

def BinD = Arg {#3} \b. ?3 {\_. Desc} b End (Rec End) (Rec End)
def Bin = Fix BinD
def BE : Bin = In {BinD} (@0, ())
def B0 : Bin -> Bin = \n. In {BinD} (@1, (n, ()))
def B1 : Bin -> Bin = \n. In {BinD} (@2, (n, ()))

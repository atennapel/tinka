import lib/desc.p

def Fix : Desc -> * = %Fix
def In : {d : Desc} -> interpDesc d (Fix d) -> Fix d = %In

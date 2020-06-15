import lib/type.p
import lib/void.p
import lib/unit.p
import lib/bool.p

-- WIP observational equality
def OEq
  : (A : *) -> A -> A -> *
  = \A. genindType {\t. t -> t -> *}
    (\_ a b. Eq a b)
    (\rec A B a b. (x : A) -> rec (B x) (a x) (b x))
    (\rec A B a b. (x : A) -> rec (B x) (a {x}) (b {x}))
    (\rec A B a b. Void)
    (\rec A B a b. Void)
    (\rec A B a b. Void)
    (\_ a b. UnitType)
    (\_ a b. UnitType)
    (\_ a b. liftBool (eqBool a b))
    (\rec I F i x y. Void)
    (\rec A B a b x y. UnitType)
    A

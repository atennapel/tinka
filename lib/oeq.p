import lib/type.p
import lib/void.p
import lib/unit.p
import lib/bool.p

-- genindType : {P : * -> *}
--    -> (((t : *) -> P t) -> P *)
--    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) -> B x))
--    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ({x : A} -> B x))
--    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) ** B x))
--    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ({x : A} ** B x))
--    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) ** {B x}))
--    -> (((t : *) -> P t) -> P Void)
--    -> (((t : *) -> P t) -> P UnitType)
--    -> (((t : *) -> P t) -> P Bool)
--    -> (((t : *) -> P t) -> (I : *) -> (F : (I -> *) -> (I -> *)) -> (i : I) -> P (IFix I F i))
--    -> (((t : *) -> P t) -> (A : *) -> (B : *) -> (a : A) -> (b : B) -> P (HEq {A} {B} a b))
--    -> (t : *) -> P t

-- * : * = * : *                                      ~> UnitType
-- (x : A) -> B x : * = (y : C) -> D y : *            ~> (A : * = C : *) ** (B : A -> * = D : C -> *)
-- (x : A) ** B x : * = (y : C) ** D y : *            ~> (A : * = C : *) ** (B : A -> * = D : C -> *)
-- Void : * = Void : *                                ~> UnitType
-- UnitType : * = UnitType : *                        ~> UnitType
-- Bool : * = Bool : *                                ~> UnitType
-- IFix I1 F1 i1 : * = IFix I2 F2 I2 : *              ~> (I1 : * = I2 : *) ** (F1 : (I1 -> *) -> (I1 -> *) = F2 : (I2 -> *) -> (I2 -> *)) ** (i1 : I1 = i2 : I2)
-- HEq {A1} {B1} a1 b1 : * = HEq {A2} {B2} a2 b2      ~> (A1 : * = A2 : *) ** (B1 : * = B2 : *) ** (a1 : A1 = a2 : A2) ** (b1 : B1 = b2 : B2)
--
-- f : (x : A1) -> B1 = g : (y : A2) -> B2            ~> (x : A1) -> (y : A2) -> (x : A1 = y : A2) -> (f x : B1 x = g x : B2 y)
-- f : (x : A1) ** B1 = g : (y : A2) ** B2            ~> (fst f : A1 = fst g : A2) ** (snd f : B1 (fst f) = snd g : B2 (fst g))
-- x : Void = y : Void                                ~> UnitType
-- x : UnitType = y : UnitType                        ~> UnitType
-- x : Bool = y : Bool                                ~> liftBool (eqBool x y)
--
-- x : IFix I1 F1 i1 = y : IFix I2 F2 i2              ~> (outIFix x : F1 I1 (IFix I1 F1) i1 = outIFix y : F2 I2 (IFix I2 F2) i2)
--
-- x : HEq {A1} {B1} a1 b1 = y : HEq {A2} {B2} a2 b2  ~> ?
--
-- otherwise                                          ~> Void if canonical

-- WIP observational equality
-- x : A = y : B
def OEq
  : (A : *) -> (B : *) -> A -> B -> *
  = \A. genindType {\A. (B : *) -> A -> B -> *}
    (\recA B. genindType {\B. * -> B -> *} -- A = *
      (\recB x. genindType {\_. * -> *} -- B = *
        (\recx y. genindType {\_. *} -- x = *
          (\recB. UnitType) -- y = *
          (\recA PA PB. Void) -- y = (x : PA) -> PB x
          (\recA PA PB. Void) -- y = {x : PA} -> PB x
          (\recA PA PB. Void) -- y = (x : PA) ** PB x
          (\recA PA PB. Void) -- y = {x : PA} ** PB x
          (\recA PA PB. Void) -- y = (x : PA) ** {PB x}
          (\_. Void) -- y = Void
          (\_. Void) -- y = UnitType
          (\_. Void) -- y = Bool
          (\rec I F i. Void) -- y = IFix I F i
          (\rec PA PB a b. Void) -- y = HEq {PA} {PB} a b
          y)
        (\recA PA PB y. Void) -- x = (x : PA) -> PB x
        (\recA PA PB y. Void) -- x = {x : PA} -> PB x
        (\recA PA PB y. Void) -- x = (x : PA) ** PB x
        (\recA PA PB y. Void) -- x = {x : PA} ** PB x
        (\recA PA PB y. Void) -- x = (x : PA) ** {PB x}
        (\_ y. Void) -- x = Void
        (\_ y. Void) -- x = UnitType
        (\_ y. Void) -- x = Bool
        (\rec I F i y. Void) -- x = IFix I F i
        (\rec PA PB a b y. Void) -- x = HEq {PA} {PB} a b
        x)
      (\recA PA PB x y. Void) -- B = (x : PA) -> PB x
      (\recA PA PB x y. Void) -- B = {x : PA} -> PB x
      (\recA PA PB x y. Void) -- B = (x : PA) ** PB x
      (\recA PA PB x y. Void) -- B = {x : PA} ** PB x
      (\recA PA PB x y. Void) -- B = (x : PA) ** {PB x}
      (\_ x y. Void) -- B = Void
      (\_ x y. Void) -- B = UnitType
      (\_ x y. Void) -- B = Bool
      (\rec I F i x y. Void) -- B = IFix I F i
      (\rec PA PB a b x y. Void) -- B = HEq {PA} {PB} a b
      B)
    (\recA PA PB B x y. Void) -- A = (x : PA) -> PB x
    (\recA PA PB B x y. Void) -- A = {x : PA} -> PB x
    (\recA PA PB B x y. Void) -- A = (x : PA) ** PB x
    (\recA PA PB B x y. Void) -- A = {x : PA} ** PB x
    (\recA PA PB B x y. Void) -- A = (x : PA) ** {PB x}
    (\_ B x y. Void) -- A = Void
    (\_ B x y. Void) -- A = UnitType
    (\_ B x y. Void) -- A = Bool
    (\rec I F i B x y. Void) -- A = IFix I F i
    (\rec PA PB a b B x y. Void) -- A = HEq {PA} {PB} a b
    A

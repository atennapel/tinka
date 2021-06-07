{--
  this file implements the following inductive-recursive type in terms of indexed types:

  data T where
    U : T
    P : (A : T) -> (El A -> T) -> T

  El : T -> *
  El U = ()
  El (P A K) = (x : El A) -> El (K x)
--}
import lib/idata;
import lib/sum;
import lib/eq;

let -T_F = \T i. Sum (Eq () i) ((-A : *) ** (TA : T A) ** (-B : A -> *) ** (K : (x : A) -> T (B x)) ** (Eq ((x : A) -> B x) i));
let -T_ = IData T_F;

let UF : T_ () = ICon {_} {T_F} (Left Refl);
let PF
  : (-A : *) -> (TA : T_ A) -> (-B : A -> *) -> (K : (x : A) -> T_ (B x)) -> T_ ((x : A) -> B x)
  = \A TA B K. ICon {_} {T_F} (Right (A, TA, B, K, Refl)); 

let elimT_
  : (-M : {i : *} -> T_ i -> *)
    -> M UF
    -> (({-i : *} -> (x : T_ i) -> M x) -> {-A : *} -> (TA : T_ A) -> {-B : A -> *} -> (K : (x : A) -> T_ (B x)) -> M (PF A TA B K))
    -> {-i : *}
    -> (x : T_ i)
    -> M x
  = \M uu pp {i} x. elimIData {_} {T_F} M (\rec {j} y. elimSum (\s. M (ICon {_} {T_F} s))
        (\q. elimEq (\e. M (ICon {_} {T_F} (Left e))) uu q)
        (\p.
          import p;
          let q = p._2._2._2._2;
          elimEq (\{k} e. M {k} (ICon {_} {T_F} (Right (A, TA, B, K, e)))) (pp @rec {A} TA {B} K) q)
      y) x;

let -T : * = (-A : *) ** T_ A;
let -El : T -> * = \x. x._1;

let U : T = ((), UF);
let P : (A : T) -> (El A -> T) -> T
  = \A K. (((x : El A) -> El (K x)), PF (El A) A._2 (\x. (K x)._1) (\x. (K x)._2));

let elimT
  : (-M : T -> *)
    -> M U
    -> (((x : T) -> M x) -> (A : T) -> (K : El A -> T) -> M (P A K))
    -> (x : T)
    -> M x
  = \M u p x. (let -i = x._1; let t = x._2; elimT_ (\{j} r. M (j, r)) u (\rec {A} TA {B} K. p (\x. rec {x._1} x._2) (A, TA) (\x. (B x, K x))) {i} t);

[]

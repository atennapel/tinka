Descriptions based on indexed functors.

Questions:
- How to implement induction principle
- How to support induction-recursion

```
Desc : (I J : *) -> *
End  : J -> Desc I J
Arg  : (A : *) -> (A -> Desc I J) -> Desc I J
Par  : I -> Desc I J -> Desc I J
HPar : (A : *) -> (A -> I) -> Desc I J -> Desc I J
Fix  : Desc (I + J) J -> Desc I J
Comp : Desc M J -> Desc I M -> Desc I J
Rix  : Desc I2 J2 -> (I2 -> I) -> (J -> J2) -> Desc I J

El : Desc I J -> (I -> *) -> J -> *
El (End j2) X j     = j == j2
El (Arg A K) X j    = (x : A) ** El (K x) X j
El (Par i K) X j    = X i ** El K X j
El (HPar A i K) X j = ((x : A) -> X (i x)) ** El K X j
El (Fix K) X j      = Data K X j
El (Comp A B) X j   = El A (El B X) j
El (Rix D f g) X j  = El D (\x. r (f x)) (g j)

Data : (D : Desc (I + J) J) -> (I -> *) -> J -> *
Con  : {D : Desc (I + J) J} -> {X : I -> *} -> {j : J} -> El D (sum X (Data D X)) X j -> Data D X j

map : {r s : I -> *} -> (D : Desc I J) -> ({i : I} -> r i -> s i) -> {j : J} -> El D r i -> El D s i
map {r} {s} (End j2) f {j} Refl = Refl
map {r} {s} (Arg A K) f {j} (x, rest) = (x, map {r} {s} (K x) f {j} rest)
map {r} {s} (Par i K) f {j} (x, rest) = (f {i} x, map {r} {s} K f {j} rest)
map {r} {s} (HPar A i K) f {j} (g, rest) = (\x. f {i} (g x), map {r} {s} K f {j} rest)
map {r} {s} (Fix K) f {j} (Con x) = Con {K} {r} {j} (map K (sum f (map (Fix K) f)) {j} x)
map {r} {s} (Comp A B) f {j} x = map {r} {s} A (map {r} {s} B f) {j} x
map {r} {s} (Rix D g h) f {j} x = map {r} {s} D (\x. f (g x)) {h j} x

BoolD : Desc Void () = Arg Bool \b. if b (End []) (End [])
Bool : * = El BoolD absurd []
True : Bool = (True, Refl)
False : Bool = (False, Refl)

NatFD : Desc (Void + ()) () = Arg Bool \b. if b (End []) (Par (inr []) (End []))
NatD : Desc Void () = Fix NatFD
Nat : * = El NatD absurd []
Z : Nat = Con (True, Refl)
S : Nat -> Nat = \n. Con (False, n)

ListFD : Desc (() + ()) () = Arg Bool \b. if b (End []) (Par (inl []) (Par (inr []) (End [])))
ListD : Desc () () = Fix ListFD
List : * -> * = \A. El ListD (\_. A) []

VecFD : Desc (() + Nat) Nat = Arg Bool \b. if b (End Z) (Arg Nat \n. Par (inl []) (Par (inr n) (End (S n))))
VecD : Desc () Nat = Fix VecFD
Vec : Nat -> * -> * = \n A. El VecD (\_. A) n
```

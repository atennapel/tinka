Fixpoint of indexed functors, with general recursion and induction.
```
Data : {I : *} -> ((I -> *) -> I -> *) -> I -> *
Con : {-I : *} -> {-F : (I -> *) -> I -> *} -> {-i : I} -> F (Data {I} F) i -> Data {I} F i
elimData
  : {-I : *} ->
    {-F : (I -> *) -> I -> *} ->
    (-P : {i : I} -> Data {I} F i -> *) ->
    (
      ({-i : I} -> (z : Data {I} F i) -> P {i} z) ->
      {-i : I} ->
      (y : F (Data {I} F) i) ->
      P {i} (Con {I} {F} {i} y)
    ) ->
    {-i : I} ->
    (x : Data {I} F i) ->
    P {i} x

-- computation
elimData {I} {F} P alg {i} (Con {I} {F} {i} x)
~>
alg (\{j} y. elimData {I} {F} P alg {j} y) {i} x
```

Non-indexed inductive-recursive fixpoint
```
Data :
  {R : *} ->
  (F : (S : *) -> (S -> R) -> *) ->
  ({-S : *} -> (T : S -> R) -> F S T -> R) ->
  *
Con :
  {-R : *} ->
  {-F : (S : *) -> (S -> R) -> *} ->
  {-G : {-S : *} -> (T : S -> R) -> F S T -> R} ->
  F (Data {R} F G) (funData {R} {F} {G}) ->
  Data {R} F G
funData :
  {-R : *} ->
  {-F : (S : *) -> (S -> R) -> *} ->
  {-G : {-S : *} -> (T : S -> R) -> F S T -> R} ->
  Data {R} F G ->
  R
elimData :
  {-R : *} ->
  {-F : (S : *) -> (S -> R) -> *} ->
  {-G : {-S : *} -> (T : S -> R) -> F S T -> R} ->
  (-P : Data {R} F G -> *) ->
  (
    ((z : Data {R} F G) -> P y) ->
    (y : F (Data {R} F G) (funData {R} {F} {G})) ->
    P (Con {R} {F} {G} y)
  ) ->
  (x : Data {R} F G) ->
  P x
```

Indexed inductive-recursive fixpoint
```
Data :
  {I : *} ->
  {R : I -> *} ->
  (F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *) ->
  ({-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i) ->
  (i : I) ->
  *
Con :
  {-I : *} ->
  {-R : I -> *} ->
  {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
  {G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
  {-i : I} ->
  F (Data {I} {R} F G) (funData {I} {R} {F} {G}) i ->
  Data {I} {R} F G i
funData :
  {-I : *} ->
  {-R : I -> *} ->
  {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
  {G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
  {-i : I} ->
  Data {I} {R} F G i ->
  R i
elimData :
  {-I : *} ->
  {-R : I -> *} ->
  {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
  {G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
  (-P : {i : I} -> Data {I} {R} F G i -> *) ->
  (
    ({-j : I} -> (z : Data {I} {R} F G j) -> P {j} z) ->
    {-i : I} ->
    (y : F (Data {I} {R} F G) (funData {I} {R} {F} {G}) i) ->
    P {i} (Con {I} {R} {F} {G} {i} y)
  ) ->
  {-i : I} ->
  (x : Data {I} {R} F G i) ->
  P {i} x

-- computation
elimData {I} {R} {F} {G} P alg {i} (Con {I} {R} {F} {G} {i} x)
~>
alg (\{j} z. elimData {I} {R} {F} {G} P alg {j} z) {i} x

funData {I} {R} {F} {G} {i} (Con {I} {R} {F} {G} {i} x)
~>
G {Data {I} {R} F G} (funData {I} {R} {F} {G}) {i} x
```

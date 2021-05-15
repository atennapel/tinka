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
```

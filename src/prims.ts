import { Expl, Impl } from './mode';
import { Val, vapp, VEq, VPi, VType, VUnitType, VBool, VTrue, VFalse, vapp2, VIIRData, vfunIIRDataPartial, VHRefl, VSymbol, vapp3, VIIRDataPartial, VIIRCon, viirF, viirG } from './values';

export type PrimConName = '*' | 'HEq' | 'HRefl' | '()' | '[]' | 'Bool' | 'True' | 'False' | 'IIRData' | 'IIRCon' | 'Symbol';
export type PrimElimName = 'elimHEq' | 'elimBool' | 'elimIIRData' | 'funIIRData' | 'eqSymbol';
export type PrimName = PrimConName | PrimElimName;

export const ErasedPrims = ['*', 'HEq', '()', 'Bool', 'IIRData', 'Symbol'];
export const isPrimErased = (name: PrimName): boolean => ErasedPrims.includes(name);

export const PrimNames: string[] = [
  '*',
  'HEq', 'HRefl', 'elimHEq',
  '()', '[]',
  'Bool', 'True', 'False', 'elimBool',
  'IIRData', 'IIRCon', 'elimIIRData', 'funIIRData',
  'Symbol', 'eqSymbol',
];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const primType = (name: PrimName): Val => {
  if (name === '*') return VType;
  // HEq : {A B : *} -> A -> B -> *
  if (name === 'HEq') return VPi(false, Impl, 'A', VType, A => VPi(false, Impl, 'B', VType, B => VPi(false, Expl, '_', A, _ => VPi(false, Expl, '_', B, _ => VType))));
  // HRefl : {-A : *} -> {-x : A} -> HEq {A} {A} x x
  if (name === 'HRefl') return VPi(true, Impl, 'A', VType, A => VPi(true, Impl, 'x', A, x => VEq(A, x, x)));
  /* 
    elimHEq : {-A : *}
      -> {-a : A}
      -> (-P : {b : A} -> HEq {A} {A} a b -> *)
      -> P {a} (HRefl {A} {a})
      -> {-b : A}
      -> (p : HEq {A} {A} a b)
      -> P {b} p
  */
  if (name === 'elimHEq')
    return VPi(true, Impl, 'A', VType, A =>
      VPi(true, Impl, 'a', A, a =>
      VPi(true, Expl, 'P', VPi(false, Impl, 'b', A, b => VPi(false, Expl, '', VEq(A, a, b), _ => VType)), P =>
      VPi(false, Expl, '_', vapp2(P, Impl, a, Expl, VHRefl(A, a)), _ =>
      VPi(true, Impl, 'b', A, b =>
      VPi(false, Expl, 'p', VEq(A, a, b), p =>
      vapp2(P, Impl, b, Expl, p)))))));
  
  if (name === '()') return VType;
  if (name === 'Bool') return VType;
  if (name === 'Symbol') return VType;

  if (name === '[]') return VUnitType;
  if (name === 'True') return VBool;
  if (name === 'False') return VBool;

  // (-P : Bool -> *) -> P True -> P False -> (b : Bool) -> P b
  if (name === 'elimBool')
    return VPi(true, Expl, 'P', VPi(false, Expl, '_', VBool, _ => VType), P =>
      VPi(false, Expl, '_', vapp(P, Expl, VTrue), _ =>
      VPi(false, Expl, '_', vapp(P, Expl, VFalse), _ =>
      VPi(false, Expl, 'b', VBool, b => vapp(P, Expl, b)))));

  /*
    {I : *} ->
    {R : I -> *} ->
    (F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *) ->
    ({-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i) ->
    I ->
    *
  */
  if (name === 'IIRData')
    return VPi(false, Impl, 'I', VType, I =>
      VPi(false, Impl, 'R', VPi(false, Expl, '_', I, _ => VType), R =>
      VPi(false, Expl, 'F', viirF(I, R), F =>
      VPi(false, Expl, '_', viirG(I, R, F), _ =>
      VPi(false, Expl, '_', I, _ => VType)))));
  /*
    {-I : *} ->
    {-R : I -> *} ->
    {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
    {-G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
    {-i : I} ->
    F (Data {I} {R} F G) (funData {I} {R} {F} {G}) i ->
    Data {I} {R} F G i
  */
  if (name === 'IIRCon')
    return VPi(true, Impl, 'I', VType, I =>
      VPi(true, Impl, 'R', VPi(false, Expl, '_', I, _ => VType), R =>
      VPi(true, Impl, 'F', viirF(I, R), F =>
      VPi(true, Impl, 'G', viirG(I, R, F), G =>
      VPi(true, Impl, 'i', I, i =>
      VPi(false, Expl, '_', vapp3(F, Expl, VIIRDataPartial(I, R, F, G), Expl, vfunIIRDataPartial(I, R, F, G), Expl, i), _ =>
      VIIRData(I, R, F, G, i)))))));
  /*
    {-I : *} ->
    {-R : I -> *} ->
    {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
    {-G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
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
  */
  if (name === 'elimIIRData')
    return VPi(true, Impl, 'I', VType, I =>
      VPi(true, Impl, 'R', VPi(false, Expl, '_', I, _ => VType), R =>
      VPi(true, Impl, 'F', viirF(I, R), F =>
      VPi(true, Impl, 'G', viirG(I, R, F), G =>
      VPi(true, Expl, 'P', VPi(false, Impl, 'i', I, i => VPi(false, Expl, '_', VIIRData(I, R, F, G, i), _ => VType)), P =>
      VPi(false, Expl, '_',
        VPi(false, Expl, '_', VPi(true, Impl, 'j', I, j => VPi(false, Expl, 'z', VIIRData(I, R, F, G, j), z => vapp2(P, Impl, j, Expl, z))), _ =>
        VPi(true, Impl, 'i', I, i =>
        VPi(false, Expl, 'y', vapp3(F, Expl, VIIRDataPartial(I, R, F, G), Expl, vfunIIRDataPartial(I, R, F, G), Expl, i), y =>
        vapp2(P, Impl, i, Expl, VIIRCon(I, R, F, G, i, y)))))
      , _ =>
      VPi(true, Impl, 'i', I, i =>
      VPi(false, Expl, 'x', VIIRData(I, R, F, G, i), x =>
      vapp2(P, Impl, i, Expl, x)))))))));
  /*
    {-I : *} ->
    {-R : I -> *} ->
    {-F : (S : I -> *) -> ({-i : I} -> S i -> R i) -> I -> *} ->
    {G : {-S : I -> *} -> (T : {-i : I} -> S i -> R i) -> {-i : I} -> F S T i -> R i} ->
    {-i : I} ->
    Data {I} {R} F G i ->
    R i
  */
  if (name === 'funIIRData')
    return VPi(true, Impl, 'I', VType, I =>
      VPi(true, Impl, 'R', VPi(false, Expl, '_', I, _ => VType), R =>
      VPi(true, Impl, 'F', viirF(I, R), F =>
      VPi(false, Impl, 'G', viirG(I, R, F), G =>
      VPi(true, Impl, 'i', I, i =>
      VPi(false, Expl, '_', VIIRData(I, R, F, G, i), _ =>
      vapp(R, Expl, i)))))));

  // eqSymbol : Symbol -> Symbol -> Bool
  if (name === 'eqSymbol') return VPi(false, Expl, '_', VSymbol, _ => VPi(false, Expl, '_', VSymbol, _ => VBool));

  return name;
};

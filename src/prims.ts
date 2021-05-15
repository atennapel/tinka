import { Expl, Impl } from './mode';
import { Val, vapp, VEq, VPi, VType, VVoid, VUnitType, VBool, VTrue, VFalse, VIData, VICon, VNat, VNatLit, VS, VFin, vapp2, VFinLit, VFS, vaddFull, VIDataPartial, IxFun, IxFunctor, VHRefl } from './values';

export type PrimConName = '*' | 'HEq' | 'HRefl' | 'Void' | '()' | '[]' | 'Bool' | 'True' | 'False' | 'IData' | 'ICon' | 'Nat' | 'Fin' | 'Symbol';
export type PrimElimName = 'elimHEq' | 'absurd' | 'elimBool' | 'elimIData' | 'S' | 'elimNat' | 'FS' | 'elimFin' | 'weakenFin';
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = [
  '*',
  'HEq', 'HRefl', 'elimHEq',
  'Void', 'absurd',
  '()', '[]',
  'Bool', 'True', 'False', 'elimBool',
  'IData', 'ICon', 'elimIData',
  'Nat', 'S', 'elimNat',
  'Fin', 'FS', 'elimFin', 'weakenFin',
  'Symbol',
];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const ErasedPrims = ['*', 'Eq', 'Void', '()', 'Bool', 'Data', 'Nat', 'Fin', 'Symbol'];
export const isPrimErased = (name: PrimName): boolean => ErasedPrims.includes(name);

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
  
  if (name === 'Void') return VType;
  if (name === '()') return VType;
  if (name === 'Bool') return VType;
  if (name === 'Symbol') return VType;

  if (name === '[]') return VUnitType;
  if (name === 'True') return VBool;
  if (name === 'False') return VBool;

  // {-A : *} -> Void -> A
  if (name === 'absurd')
    return VPi(true, Impl, 'A', VType, A => VPi(false, Expl, '_', VVoid, _ => A));

  // (-P : Bool -> *) -> P True -> P False -> (b : Bool) -> P b
  if (name === 'elimBool')
    return VPi(true, Expl, 'P', VPi(false, Expl, '_', VBool, _ => VType), P =>
      VPi(false, Expl, '_', vapp(P, Expl, VTrue), _ =>
      VPi(false, Expl, '_', vapp(P, Expl, VFalse), _ =>
      VPi(false, Expl, 'b', VBool, b => vapp(P, Expl, b)))));

  // {I : *} -> ((I -> *) -> I -> *) -> I -> *
  if (name === 'IData')
    return VPi(false, Impl, 'I', VType, I => VPi(false, Expl, '_', IxFunctor(I), _ => IxFun(I)));
  // {-I : *} -> {-F : (I -> *) -> I -> *} -> {-i : I} -> F (IData {I} F) i -> IData {I} F i
  if (name === 'ICon')
    return VPi(true, Impl, 'I', VType, I =>
      VPi(true, Impl, 'F', IxFunctor(I), F =>
      VPi(true, Impl, 'i', I, i =>
      VPi(false, Expl, '_', vapp2(F, Expl, VIDataPartial(I, F), Expl, i), _ =>
      VIData(I, F, i)))));
  /*
    {-I : *} ->
    {-F : (I -> *) -> I -> *} ->
    (-P : {i : I} -> IData {I} F i -> *) ->
    (
      ({-i : I} -> (z : IData {I} F i) -> P {i} z) ->
      {-i : I} ->
      (y : F (IData {I} F) i) ->
      P {i} (ICon {I} {F} {i} y)
    ) ->
    {-i : I} ->
    (x : IData {I} F i) ->
    P {i} x
  */
  if (name === 'elimIData')
    return VPi(true, Impl, 'I', VType, I =>
      VPi(true, Impl, 'F', IxFunctor(I), F =>
      VPi(true, Expl, 'P', VPi(false, Impl, 'i', I, i => VPi(false, Expl, '_', VIData(I, F, i), _ => VType)), P =>
      VPi(false, Expl, '_', VPi(false, Expl, '_', VPi(true, Impl, 'i', I, i => VPi(false, Expl, 'z', VIData(I, F, i), z => vapp2(P, Impl, i, Expl, z))), _ => VPi(true, Impl, 'i', I, i => VPi(false, Expl, 'y', vapp2(F, Expl, VIDataPartial(I, F), Expl, i), y => vapp2(P, Impl, i, Expl, VICon(I, F, i, y))))), _ =>
      VPi(true, Impl, 'i', I, i =>
      VPi(false, Expl, 'x', VIData(I, F, i), x =>
      vapp2(P, Impl, i, Expl, x)))))));

  if (name === 'Nat') return VType;
  if (name === 'S') return VPi(false, Expl, '_', VNat, _ => VNat);
  // elimNat : (-P : Nat -> *) -> P 0 -> (((k : Nat) -> P k) -> (m : Nat) -> P (S m)) -> (n : Nat) -> P n
  if (name === 'elimNat')
    return VPi(true, Expl, 'P', VPi(false, Expl, '_', VNat, _ => VType), P =>
      VPi(false, Expl, '_', vapp(P, Expl, VNatLit(0n)), _ =>
      VPi(false, Expl, '_', VPi(false, Expl, '_', VPi(false, Expl, 'k', VNat, k => vapp(P, Expl, k)), _ => VPi(false, Expl, 'm', VNat, m => vapp(P, Expl, VS(m)))), _ =>
      VPi(false, Expl, 'n', VNat, n => vapp(P, Expl, n)))));

  if (name === 'Fin') return VPi(false, Expl, '_', VNat, _ => VType);
  // FS : {-n : Nat} -> Fin n -> Fin (S n)
  if (name === 'FS') return VPi(true, Impl, 'n', VNat, n => VPi(false, Expl, '_', VFin(n), _ => VFin(VS(n))));
  /*
    elimFin :
      (-P : (n : Nat) -> Fin n -> *) ->
      ({-m : Nat} -> P (S m) (0/m/m)) ->
      (({-k : Nat} -> (y : Fin k) -> P k y) -> {-k : Nat} -> (y : Fin k) -> P (S k) (FS {k} y))
      -> {-n : Nat} -> (x : Fin n) -> P n x
  */
  if (name === 'elimFin')
    return VPi(true, Expl, 'P', VPi(false, Expl, 'n', VNat, n => VPi(false, Expl, '_', VFin(n), _ => VType)), P =>
      VPi(false, Expl, '_', VPi(true, Impl, 'm', VNat, m => vapp2(P, Expl, VS(m), Expl, VFinLit(0n, m, m))), _ =>
      VPi(false, Expl, '_', VPi(false, Expl, '_', VPi(true, Impl, 'k', VNat, k => VPi(false, Expl, 'y', VFin(k), y => vapp2(P, Expl, k, Expl, y))), _ => VPi(true, Impl, 'k', VNat, k => VPi(false, Expl, 'y', VFin(k), y => vapp2(P, Expl, VS(k), Expl, VFS(k, y))))), _ =>
      VPi(true, Impl, 'n', VNat, n =>
      VPi(false, Expl, 'x', VFin(n), x =>
      vapp2(P, Expl, n, Expl, x))))));
  // weakenFin : {-m -n : Nat} -> Fin n -> Fin (add m n) 
  if (name === 'weakenFin') return VPi(true, Impl, 'm', VNat, m => VPi(true, Impl, 'n', VNat, n => VPi(false, Expl, '_', VFin(n), _ => VFin(vaddFull(m, n)))));

  return name;
};

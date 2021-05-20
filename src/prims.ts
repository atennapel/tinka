import { Expl, Impl } from './mode';
import { Val, vapp, VEq, VPi, VType, VVoid, VUnitType, VBool, VTrue, VFalse, VNat, VNatLit, VS, VFin, vapp2, VIIRData, VFinLit, VFS, vaddFull, vfunIIRDataPartial, VHRefl, VSymbol, vapp3, VIIRDataPartial, VIIRCon, viirF, viirG } from './values';

export type PrimConName = '*' | 'HEq' | 'HRefl' | 'Void' | '()' | '[]' | 'Bool' | 'True' | 'False' | 'IIRData' | 'IIRCon' | 'Nat' | 'Fin' | 'Symbol';
export type PrimElimName = 'elimHEq' | 'absurd' | 'elimBool' | 'elimIIRData' | 'funIIRData' | 'S' | 'elimNat' | 'FS' | 'elimFin' | 'weakenFin' | 'eqSymbol';
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = [
  '*',
  'HEq', 'HRefl', 'elimHEq',
  'Void', 'absurd',
  '()', '[]',
  'Bool', 'True', 'False', 'elimBool',
  'IIRData', 'IIRCon', 'elimIIRData', 'funIIRData',
  'Nat', 'S', 'elimNat',
  'Fin', 'FS', 'elimFin', 'weakenFin',
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
  */
  if (name === 'elimIIRData')
    return VPi(true, Impl, 'I', VType, I =>
      VPi(true, Impl, 'R', VPi(false, Expl, '_', I, _ => VType), R =>
      VPi(true, Impl, 'F', viirF(I, R), F =>
      VPi(false, Impl, 'G', viirG(I, R, F), G =>
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

  // eqSymbol : Symbol -> Symbol -> Bool
  if (name === 'eqSymbol') return VPi(false, Expl, '_', VSymbol, _ => VPi(false, Expl, '_', VSymbol, _ => VBool));

  return name;
};

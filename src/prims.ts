import { Expl, Impl } from './mode';
import { Val, vapp, VEq, VPi, VType, VRefl, VVoid, VUnitType, VBool, VTrue, VFalse, VData, VCon, VNat, VNatLit, VS, VFin, vapp2, VFinLit, VFS, vaddFull } from './values';

export type PrimConName = '*' | 'Eq' | 'Refl' | 'Void' | '()' | '[]' | 'Bool' | 'True' | 'False' | 'Data' | 'Con' | 'Nat' | 'Fin';
export type PrimElimName = 'elimEq' | 'absurd' | 'elimBool' | 'elimData' | 'S' | 'elimNat' | 'FS' | 'elimFin' | 'weakenFin';
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = [
  '*',
  'Eq', 'Refl', 'elimEq',
  'Void', 'absurd',
  '()', '[]',
  'Bool', 'True', 'False', 'elimBool',
  'Data', 'Con', 'elimData',
  'Nat', 'S', 'elimNat',
  'Fin', 'FS', 'elimFin', 'weakenFin',
];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const ErasedPrims = ['*', 'Eq', 'Void', '()', 'Bool', 'Data', 'Nat', 'Fin'];
export const isPrimErased = (name: PrimName): boolean => ErasedPrims.includes(name);

export const primType = (name: PrimName): Val => {
  if (name === '*') return VType;
  // Eq : {A : *} -> A -> A -> *
  if (name === 'Eq') return VPi(false, Impl, 'A', VType, A => VPi(false, Expl, '_', A, _ => VPi(false, Expl, '_', A, _ => VType)));
  // Refl : {-A : *} -> {-x : A} -> Eq {A} x x
  if (name === 'Refl') return VPi(true, Impl, 'A', VType, A => VPi(true, Impl, 'x', A, x => VEq(A, x, x)));
  // elimEq : {-A : *} -> (-P : (x y : A) -> Eq {A} x y -> *) -> ({-x : A} -> P x x (Refl {A} {x})) -> {-x -y : A} -> (p : Eq {A} x y) -> P x y p
  if (name === 'elimEq')
    return VPi(true, Impl, 'A', VType, A =>
      VPi(true, Expl, 'P', VPi(false, Expl, 'x', A, x => VPi(false, Expl, 'y', A, y => VPi(false, Expl, '_', VEq(A, x, y), _ => VType))), P =>
      VPi(false, Expl, '_', VPi(true, Impl, 'x', A, x => vapp(vapp(vapp(P, Expl, x), Expl, x), Expl, VRefl(A, x))), _ =>
      VPi(true, Impl, 'x', A, x =>
      VPi(true, Impl, 'y', A, y =>
      VPi(false, Expl, 'p', VEq(A, x, y), p =>
      vapp(vapp(vapp(P, Expl, x), Expl, y), Expl, p)))))));
  
  if (name === 'Void') return VType;
  if (name === '()') return VType;
  if (name === 'Bool') return VType;

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

  // (* -> *) -> *
  if (name === 'Data')
    return VPi(false, Expl, '_', VPi(false, Expl, '_', VType, _ => VType), _ => VType);
  // {-F : * -> *} -> F (Data F) -> Data F
  if (name === 'Con')
    return VPi(true, Impl, 'F', VPi(false, Expl, '_', VType, _ => VType), F => VPi(false, Expl, '_', vapp(F, Expl, VData(F)), _ => VData(F)));

  /* {-F : * -> *}
    -> (-map : {-A -B : *} -> (A -> B) -> F A -> F B)
    -> (-P : Data F -> *)
    -> (
      {-R : *}
      -> (out : R -> Data F)
      -> ((z : R) -> P (out z))
      -> (y : F R)
      -> P (Con {F} (map {R} {Data F} out y))
    )
    -> (x : Data F)
    -> P x*/
  if (name === 'elimData')
    return VPi(true, Impl, 'F', VPi(false, Expl, '_', VType, _ => VType), F =>
      VPi(true, Expl, 'map', VPi(true, Impl, 'A', VType, A => VPi(true, Impl, 'B', VType, B => VPi(false, Expl, '_', VPi(false, Expl, '_', A, _ => B), _ => VPi(false, Expl, '_', vapp(F, Expl, A), _ => vapp(F, Expl, B))))), map =>
      VPi(true, Expl, 'P', VPi(false, Expl, '_', VData(F), _ => VType), P =>
      VPi(false, Expl, '_',
        VPi(true, Impl, 'R', VType, R =>
        VPi(false, Expl, 'out', VPi(false, Expl, '_', R, _ => VData(F)), out =>
        VPi(false, Expl, '_', VPi(false, Expl, 'z', R, z => vapp(P, Expl, vapp(out, Expl, z))), _ =>
        VPi(false, Expl, 'y', vapp(F, Expl, R), y =>
        vapp(P, Expl, VCon(F, vapp(vapp(vapp(vapp(map, Impl, R), Impl, VData(F)), Expl, out), Expl, y)))))))
      , _ =>
      VPi(false, Expl, 'x', VData(F), x => vapp(P, Expl, x))))));

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

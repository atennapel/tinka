import { Expl, Impl } from './mode';
import { Val, vapp, VEq, VPi, VType, VRefl, VVoid, VUnitType, VBool, VTrue, VFalse, VData, VCon } from './values';

export type PrimConName = '*' | 'Eq' | 'Refl' | 'Void' | '()' | '[]' | 'Bool' | 'True' | 'False' | 'Data' | 'Con' | 'Nat';
export type PrimElimName = 'elimEq' | 'absurd' | 'elimBool' | 'elimData';
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = ['*', 'Eq', 'Refl', 'elimEq', 'Void', 'absurd', '()', '[]', 'Bool', 'True', 'False', 'elimBool', 'Data', 'Con', 'elimData', 'Nat'];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const ErasedPrims = ['*', 'Eq', 'Void', '()', 'Bool', 'Data', 'Nat'];
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

  return name;
};

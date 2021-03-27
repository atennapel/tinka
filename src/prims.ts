import { Expl } from './mode';
import { Val, vapp, VEq, VPi, VType, VUnitType, VRefl, VNat, VS, VZ } from './values';

export type PrimConName = '*' | '()' | 'Unit' | 'Eq' | 'Refl' | 'Nat' | 'Z' | 'S';
export type PrimElimName = 'elimEq' | 'elimNat';
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = ['*', '()', 'Unit', 'Eq', 'Refl', 'elimEq', 'Nat', 'Z', 'S', 'elimNat'];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const ErasedPrims = ['*', '()', 'Eq', 'Nat'];
export const isPrimErased = (name: PrimName): boolean => ErasedPrims.includes(name);

export const primType = (name: PrimName): Val => {
  if (name === '*') return VType;
  if (name === '()') return VType;
  if (name === 'Unit') return VUnitType;
  // Eq : (A : *) -> A -> A -> *
  if (name === 'Eq') return VPi(false, Expl, 'A', VType, A => VPi(false, Expl, '_', A, _ => VPi(false, Expl, '_', A, _ => VType)));
  // Refl : (-A : *) -> (-x : A) -> Eq A x x
  if (name === 'Refl') return VPi(true, Expl, 'A', VType, A => VPi(true, Expl, 'x', A, x => VEq(A, x, x)));
  // (-A : *) -> (-P : (x y : A) -> Eq A x y -> *) -> ((-x : A) -> P x x (Refl A x)) -> (-x -y : A) -> (p : Eq A x y) -> P x y p
  if (name === 'elimEq')
    return VPi(true, Expl, 'A', VType, A =>
      VPi(true, Expl, 'P', VPi(false, Expl, 'x', A, x => VPi(false, Expl, 'y', A, y => VPi(false, Expl, '_', VEq(A, x, y), _ => VType))), P =>
      VPi(false, Expl, '_', VPi(true, Expl, 'x', A, x => vapp(vapp(vapp(P, Expl, x), Expl, x), Expl, VRefl(A, x))), _ =>
      VPi(true, Expl, 'x', A, x =>
      VPi(true, Expl, 'y', A, y =>
      VPi(false, Expl, 'p', VEq(A, x, y), p =>
      vapp(vapp(vapp(P, Expl, x), Expl, y), Expl, p)))))));
  if (name === 'Nat') return VType;
  if (name === 'Z') return VNat;
  if (name === 'S') return VPi(false, Expl, '_', VNat, _ => VNat);
  // (-P : Nat -> *) -> P Z -> ((m : Nat) -> P m -> P (S m)) -> (n : Nat) -> P n
  if (name === 'elimNat')
    return VPi(true, Expl, 'P', VPi(false, Expl, '_', VNat, _ => VType), P =>
      VPi(false, Expl, '_', vapp(P, Expl, VZ), _ =>
      VPi(false, Expl, '_', VPi(false, Expl, 'm', VNat, m => VPi(false, Expl, '_', vapp(P, Expl, m), _ => vapp(P, Expl, VS(m)))), _ =>
      VPi(false, Expl, 'n', VNat, n =>
      vapp(P, Expl, n)))));
  return name;
};

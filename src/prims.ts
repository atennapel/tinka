import { Expl } from './mode';
import { Val, vapp, VEq, VPi, VType, VRefl, VNat, VS, VZ, VFin, VFZ, VFS } from './values';

export type PrimConName = '*' | 'Eq' | 'Refl' | 'Nat' | 'Z' | 'S' | 'Fin' | 'FZ' | 'FS';
export type PrimElimName = 'elimEq' | 'elimNat' | 'elimFin';
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = ['*', 'Eq', 'Refl', 'elimEq', 'Nat', 'Z', 'S', 'elimNat', 'Fin', 'FZ', 'FS', 'elimFin'];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const ErasedPrims = ['*', 'Eq', 'Nat'];
export const isPrimErased = (name: PrimName): boolean => ErasedPrims.includes(name);

export const primType = (name: PrimName): Val => {
  if (name === '*') return VType;
  // Eq : (A : *) -> A -> A -> *
  if (name === 'Eq') return VPi(false, Expl, 'A', VType, A => VPi(false, Expl, '_', A, _ => VPi(false, Expl, '_', A, _ => VType)));
  // Refl : (-A : *) -> (-x : A) -> Eq A x x
  if (name === 'Refl') return VPi(true, Expl, 'A', VType, A => VPi(true, Expl, 'x', A, x => VEq(A, x, x)));
  // elimEq : (-A : *) -> (-P : (x y : A) -> Eq A x y -> *) -> ((-x : A) -> P x x (Refl A x)) -> (-x -y : A) -> (p : Eq A x y) -> P x y p
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
  // elimNat : (-P : Nat -> *) -> P Z -> ((m : Nat) -> P m -> P (S m)) -> (n : Nat) -> P n
  if (name === 'elimNat')
    return VPi(true, Expl, 'P', VPi(false, Expl, '_', VNat, _ => VType), P =>
      VPi(false, Expl, '_', vapp(P, Expl, VZ), _ =>
      VPi(false, Expl, '_', VPi(false, Expl, 'm', VNat, m => VPi(false, Expl, '_', vapp(P, Expl, m), _ => vapp(P, Expl, VS(m)))), _ =>
      VPi(false, Expl, 'n', VNat, n =>
      vapp(P, Expl, n)))));
  // Fin : Nat -> *
  if (name === 'Fin') return VPi(false, Expl, '_', VNat, _ => VType);
  // FZ : (-n : Nat) -> Fin (S n)
  if (name === 'FZ') return VPi(true, Expl, 'n', VNat, n => VFin(VS(n)));
  // FS : (-n : Nat) -> Fin n -> Fin (S n)
  if (name === 'FS') return VPi(true, Expl, 'n', VNat, n => VPi(false, Expl, '_', VFin(n), _ => VFin(VS(n))));
  // elimFin : (-P : (n : Nat) -> Fin n -> *) -> ((-n : Nat) -> P (S n) (FZ n)) -> ((-n : Nat) -> (y : Fin n) -> P n y -> P (S n) (FS n y)) -> (-n : Nat) -> (x : Fin n) -> P n x
  if (name === 'elimFin')
    return VPi(true, Expl, 'P', VPi(false, Expl, 'n', VNat, n => VPi(false, Expl, '_', VFin(n), _ => VType)), P =>
      VPi(false, Expl, '_', VPi(true, Expl, 'n', VNat, n => vapp(vapp(P, Expl, VS(n)), Expl, VFZ(n))), _ =>
      VPi(false, Expl, '_', VPi(true, Expl, 'n', VNat, n => VPi(false, Expl, 'y', VFin(n), y => VPi(false, Expl, '_', vapp(vapp(P, Expl, n), Expl, y), _ => vapp(vapp(P, Expl, VS(n)), Expl, VFS(n, y))))), _ =>
      VPi(true, Expl, 'n', VNat, n =>
      VPi(false, Expl, 'x', VFin(n), x =>
      vapp(vapp(P, Expl, n), Expl, x))))));
  return name;
};

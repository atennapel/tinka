import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, VType, vheq, VNat, VZ, VS, VFin, VFZ, VFS, VIFix } from './domain';
import { impossible } from './utils/utils';

const primTypes: { [K in PrimName]: () => Val } = {
  // {a : *} -> {b : a -> *} -> (((x : a) -> b x) -> ((x : a) -> b x)) -> (x : a) -> b x
  'drec': () =>
    VPi(true, 'a', VType, a =>
    VPi(true, 'b', VPi(false, '_', a, _ => VType), b =>
    VPi(false, '_', VPi(false, '_', VPi(false, 'x', a, x => vapp(b, false, x)), _ => VPi(false, 'x', a, x => vapp(b, false, x))), _ =>
    VPi(false, 'x', a, x => vapp(b, false, x))))),
  // {a : *} -> {b : a -> *} -> (({x : a} -> b x) -> ({x : a} -> b x)) -> {x : a} -> b x
  'dreci': () =>
    VPi(true, 'a', VType, a =>
    VPi(true, 'b', VPi(false, '_', a, _ => VType), b =>
    VPi(false, '_', VPi(false, '_', VPi(true, 'x', a, x => vapp(b, false, x)), _ => VPi(true, 'x', a, x => vapp(b, false, x))), _ =>
    VPi(true, 'x', a, x => vapp(b, false, x))))),

  // {A : *} -> {B : *} -> A -> B -> *
  'HEq': () => VPi(true, 'A', VType, A => VPi(true, 'B', VType, B => VPi(false, '_', A, _ => VPi(false, '_', B, _ => VType)))),
  // {A : *} -> {a : A} -> HEq {A} {A} a a
  'ReflHEq': () => VPi(true, 'A', VType, A => VPi(true, 'a', A, a => vheq(A, A, a, a))),
  // {A : *} -> {a : A} -> {P : (b : A) -> HEq {A} {A} a b -> *} -> P a (ReflHEq {A} {a}) -> {b : A} -> (q : HEq {A} {A} a b) -> P b q
  'elimHEq': () =>
    VPi(true, 'A', VType, A =>
    VPi(true, 'a', A, a =>
    VPi(true, 'P', VPi(false, 'b', A, b => VPi(false, '_', vheq(A, A, a, b), _ => VType)), P =>
    VPi(false, '_', vapp(vapp(P, false, a), false, vapp(vapp(VPrim('ReflHEq'), true, A), true, a)), _ =>
    VPi(true, 'b', A, b =>
    VPi(false, 'p', vheq(A, A, a, b), p =>
    vapp(vapp(P, false, b), false, p))))))),

  'Nat': () => VType,
  'Z': () => VNat,
  'S': () => VPi(false, '_', VNat, _ => VNat),
  // {P : Nat -> *} -> P Z -> ((m : Nat) -> P (S m)) -> (n : Nat) -> P n
  'elimNat': () =>
    VPi(true, 'P', VPi(false, '_', VNat, _ => VType), P =>
    VPi(false, '_', vapp(P, false, VZ), _ =>
    VPi(false, '_', VPi(false, 'm', VNat, m => vapp(P, false, VS(m))), _ =>
    VPi(false, 'n', VNat, n => vapp(P, false, n))))),

  'Fin': () => VPi(false, '_', VNat, _ => VType),
  'FZ': () => VPi(true, 'n', VNat, n => vapp(VFin, false, VS(n))),
  'FS': () => VPi(true, 'n', VNat, n => VPi(false, '_', vapp(VFin, false, n), _ => vapp(VFin, false, VS(n)))),
  // {P : (n : Nat) -> Fin n -> *} -> ({m : Nat} -> P (S m) (FZ {m})) -> ({m : Nat} -> (y : Fin m) -> P (S m) (FS {m} y)) -> {n : Nat} -> (x : Fin n) -> P n f
  'elimFin': () =>
    VPi(true, 'P', VPi(false, 'n', VNat, n => VPi(false, '_', vapp(VFin, false, n), _ => VType)), P =>
    VPi(false, '_', VPi(true, 'm', VNat, m => vapp(vapp(P, false, VS(m)), false, vapp(VFZ, true, m))), _ =>
    VPi(false, '_', VPi(true, 'm', VNat, m => VPi(false, 'y', vapp(VFin, false, m), y => vapp(vapp(P, false, VS(m)), false, vapp(vapp(VFS, true, m), false, y)))), _ =>
    VPi(true, 'n', VNat, n =>
    VPi(false, 'x', vapp(VFin, false, n), x => vapp(vapp(P, false, n), false, x)))))),

  // {P : Fin 0 -> *} -> (x : Fin 0) -> P x
  'elimFin0': () =>
    VPi(true, 'P', VPi(false, '_', vapp(VFin, false, VZ), _ => VType), P =>
    VPi(false, 'x', vapp(VFin, false, VZ), x => vapp(P, false, x))),

  // (I : *) -> ((I -> *) -> I -> *) -> I -> *
  'IFix': () =>
    VPi(false, 'I', VType, I =>
    VPi(false, '_', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), _ =>
    VPi(false, '_', I, _ => VType))),
  // {I : *} -> {F : (I -> *) -> I -> *} -> {i : I} -> F (IFix {I} F) i IFix {I} F i
  'IIn': () =>
    VPi(true, 'I', VType, I =>
    VPi(true, 'F', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), F =>
    VPi(true, 'i', I, i =>
    VPi(false, '_', vapp(vapp(F, false, vapp(vapp(VIFix, false, I), false, F)), false, i), _ =>
    vapp(vapp(vapp(VIFix, false, I), false, F), false, i))))),
  /*
    elimIFix
    : {I : *}
    -> {F : (I -> *) -> (I -> *)}
    -> {P : (i : I) -> IFix I F i -> P}
    -> (
      -> {i : I}
      -> (z : F (IFix I F) i)
      -> P i (IIn {I} {F} {i} z)
    )
    -> {i : I}
    -> (x : IFix I F i)
    -> P i x
  */
  'elimIFix': () =>
    VPi(true, 'I', VType, I =>
    VPi(true, 'F', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), F =>
    VPi(true, 'P', VPi(false, 'i', I, i => VPi(false, '_', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), _ => VType)), P =>
    VPi(false, '_',
      VPi(true, 'i', I, i =>
      VPi(false, 'z', vapp(vapp(F, false, vapp(vapp(VIFix, false, I), false, F)), false, i), z =>
      vapp(vapp(P, false, i), false, vapp(vapp(vapp(vapp(VPrim('IIn'), true, I), true, F), true, i), false, z))))
    , _ =>
    VPi(true, 'i', I, i =>
    VPi(false, 'x', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), x =>
    vapp(vapp(P, false, i), false, x))))))),
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

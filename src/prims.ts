import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, VType, VUnitType, vheq, VNat, VNatLit, vsucc } from './domain';
import { impossible } from './utils/utils';

const primTypes: { [K in PrimName]: () => Val } = {
  'UnitType': () => VType,
  'Unit': () => VUnitType,

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
  'S': () => VPi(false, '_', VNat, _ => VNat),
  /*
  {P : Nat -> *}
    -> P Z
    -> (((k : Nat) -> P k) -> (m : Nat) -> P (S m))
    -> (n : Nat)
    -> P n
  */
  'genindNat': () =>
    VPi(true, 'P', VPi(false, '_', VNat, _ => VType), P =>
    VPi(false, '_', vapp(P, false, VNatLit(0n)), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 'k', VNat, k => vapp(P, false, k)), _ => VPi(false, 'm', VNat, m => vapp(P, false, vsucc(m)))), _ =>
    VPi(false, 'n', VNat, n =>
    vapp(P, false, n))))),
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

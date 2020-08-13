import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, VType, VUnitType, vheq } from './domain';
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
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

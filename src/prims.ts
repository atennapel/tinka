import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, VType, VIFix, VVoid, VUnitType, VUnit, VBool, VTrue, VFalse, vheq, VSigma } from './domain';
import { impossible } from './utils/utils';

const primTypes: { [K in PrimName]: () => Val } = {
  'unsafeCast': () => VPi(true, 'a', VType, a => VPi(true, 'b', VType, b => VPi(false, '_', b, _ => a))),

  'Void': () => VType,
  // indVoid : {P : Void -> *} -> (x : Void) -> P x
  'indVoid': () => VPi(true, 'P', VPi(false, '_', VVoid, _ => VType), P => VPi(false, 'x', VVoid, x => vapp(P, false, x))),

  'UnitType': () => VType,
  'Unit': () => VUnitType,
  // indUnit : {P : UnitType -> *} -> P Unit -> (u : UnitType) -> P u
  'indUnit': () => VPi(true, 'P', VPi(false, '_', VUnitType, _ => VType), P => VPi(false, '_', vapp(P, false, VUnit), _ => VPi(false, 'x', VUnitType, x => vapp(P, false, x)))),

  'Bool': () => VType,
  'True': () => VBool,
  'False': () => VBool,
  // indBool : {P : Bool -> *} -> P True -> P False -> (b : Bool) -> P b
  'indBool': () => VPi(true, 'P', VPi(false, '_', VBool, _ => VType), P => VPi(false, '_', vapp(P, false, VTrue), _ => VPi(false, '_', vapp(P, false, VFalse), _ => VPi(false, 'x', VBool, x => vapp(P, false, x))))),

  'IFix': () => VPi(false, 'I', VType, I => VPi(false, '_', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), _ => VPi(false, '_', I, _ => VType))),
  'IIn': () =>
    VPi(true, 'I', VType, I =>
    VPi(true, 'F', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), F =>
    VPi(true, 'i', I, i =>
    VPi(false, '_', vapp(vapp(F, false, vapp(vapp(VIFix, false, I), false, F)), false, i), _ =>
    vapp(vapp(vapp(VIFix, false, I), false, F), false, i))))),
  /*
    genindIFix
    : {I : *}
    -> {F : (I -> *) -> (I -> *)}
    -> {P : (i : I) -> IFix I F i -> P}
    -> (
      ({i : I} -> (y : IFix I F i) -> P i y)
      -> {i : I}
      -> (z : F (IFix I F) i)
      -> P i (IIn {I} {F} {i} z)
    )
    -> {i : I}
    -> (x : IFix I F i)
    -> P i x
  */
  'genindIFix': () =>
    VPi(true, 'I', VType, I =>
    VPi(true, 'F', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), F =>
    VPi(true, 'P', VPi(false, 'i', I, i => VPi(false, '_', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), _ => VType)), P =>
    VPi(false, '_',
      VPi(false, '_', VPi(true, 'i', I, i => VPi(false, 'y', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), y => vapp(vapp(P, false, i), false, y))), _ =>
      VPi(true, 'i', I, i =>
      VPi(false, 'z', vapp(vapp(F, false, vapp(vapp(VIFix, false, I), false, F)), false, i), z =>
      vapp(vapp(P, false, i), false, vapp(vapp(vapp(vapp(VPrim('IIn'), true, I), true, F), true, i), false, z)))))
    , _ =>
    VPi(true, 'i', I, i =>
    VPi(false, 'x', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), x =>
    vapp(vapp(P, false, i), false, x))))))),

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

  /*
  indType
  : {P : * -> *}
    -> (((t : *) -> P t) -> P *)
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) -> B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ({x : A} -> B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) ** B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ({x : A} ** B x))
    -> (((t : *) -> P t) -> (A : *) -> (B : A -> *) -> P ((x : A) ** {B x}))
    -> (((t : *) -> P t) -> P Void)
    -> (((t : *) -> P t) -> P UnitType)
    -> (((t : *) -> P t) -> P Bool)
    -> (((t : *) -> P t) -> (I : *) -> (F : (I -> *) -> (I -> *)) -> (i : *) -> P (IFix I F i))
    -> (((t : *) -> P t) -> (A : *) -> (B : *) -> (a : A) -> (b : B) -> P (HEq {A} {B} a b))
    -> (t : *) -> P t
  */
  genindType: () =>
    VPi(true, 'P', VPi(false, '_', VType, _ => VType), P =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => vapp(P, false, VType)), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'A', VType, A => VPi(false, 'B', VPi(false, '_', A, _ => VType), B => vapp(P, false, VPi(false, 'x', A, x => vapp(B, false, x)))))), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'A', VType, A => VPi(false, 'B', VPi(false, '_', A, _ => VType), B => vapp(P, false, VPi(true, 'x', A, x => vapp(B, false, x)))))), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'A', VType, A => VPi(false, 'B', VPi(false, '_', A, _ => VType), B => vapp(P, false, VSigma(false, false, 'x', A, x => vapp(B, false, x)))))), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'A', VType, A => VPi(false, 'B', VPi(false, '_', A, _ => VType), B => vapp(P, false, VSigma(true, false, 'x', A, x => vapp(B, false, x)))))), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'A', VType, A => VPi(false, 'B', VPi(false, '_', A, _ => VType), B => vapp(P, false, VSigma(false, true, 'x', A, x => vapp(B, false, x)))))), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => vapp(P, false, VVoid)), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => vapp(P, false, VUnitType)), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => vapp(P, false, VBool)), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'I', VType, I => VPi(false, 'F', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), F => VPi(false, 'i', I, i => vapp(P, false, vapp(vapp(vapp(VIFix, false, I), false, F), false, i)))))), _ =>
    VPi(false, '_', VPi(false, '_', VPi(false, 't', VType, t => vapp(P, false, t)), _ => VPi(false, 'A', VType, A => VPi(false, 'B', VType, B => VPi(false, 'a', A, a => VPi(false, 'b', B, b => vapp(P, false, vheq(A, B, a, b))))))), _ =>
    VPi(false, 't', VType, t => vapp(P, false, t)))))))))))))),
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, VType, VIFix, VEnum, VElem } from './domain';
import { impossible } from './utils/utils';

const primTypes: { [K in PrimName]: () => Val } = {
  '*': () => VType,

  'unsafeCast': () => VPi(true, 'a', VType, a => VPi(true, 'b', VType, b => VPi(false, '_', b, _ => a))),

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

  // {u : UnitType} -> {f : UnitType -> *} -> f u -> f Unit
  'uniqUnit': () =>
    VPi(true, 'u', VEnum(1), u =>
    VPi(true, 'f', VPi(false, '_', VEnum(1), _ => VType), f =>
    VPi(false, '_', vapp(f, false, u), _ =>
    vapp(f, false, VElem(0, 1))))),
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

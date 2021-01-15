import { Expl } from './mode';
import { Name } from './names';
import { many, multiply, Usage, zero } from './usage';
import { Lazy } from './utils/Lazy';
import { mapObj, terr } from './utils/utils';
import { Val, VType, VUnitType, VBool, isVTrue, isVFalse, isVUnit, vapp, force, VVoid, VPi, VUnit, VTrue, VFalse, vinst, VPair, VPropEq, VRefl } from './values';

export type PrimName = 'Type' | 'Void' | '()' | '*' | 'Bool' | 'True' | 'False';
export const PrimNames: string[] = ['Type', 'Void', '()', '*', 'Bool', 'True', 'False'];

export type PrimElimName = 'elimSigma' | 'elimPropEq' | 'elimVoid' | 'elimUnit' | 'elimBool';
export const PrimElimNames: string[] = ['elimSigma', 'elimPropEq', 'elimVoid', 'elimUnit', 'elimBool'];

export const isPrimName = (name: Name): name is PrimName => PrimNames.includes(name);
export const isPrimElimName = (name: Name): name is PrimElimName => PrimElimNames.includes(name);

const primTypes: { [K in PrimName]: Lazy<Val> } = mapObj({
  Type: () => VType,

  Void: () => VType,

  '()': () => VType,
  '*': () => VUnitType,

  Bool: () => VType,
  True: () => VBool,
  False: () => VBool,
}, Lazy.from);

export const primElim = (name: PrimElimName, usage: Usage, motive: Val, scrut: Val, cases: Val[]): Val | null => {
  if (name === 'elimUnit') {
    if (isVUnit(scrut)) return cases[0];  
  }
  if (name === 'elimBool') {
    if (isVTrue(scrut)) return cases[0];
    if (isVFalse(scrut)) return cases[1];
  }
  if (name === 'elimSigma') {
    if (scrut.tag === 'VPair') return vapp(vapp(cases[0], Expl, scrut.fst), Expl, scrut.snd);
  }
  if (name === 'elimPropEq') {
    if (scrut.tag === 'VRefl') return vapp(cases[0], Expl, scrut.val);
  }
  return null;
};

export type PrimElimTypeInfo = [number, (ty_: Val, usage: Usage) => [Val, (vmotive: Val, vscrut: Val) => [Val[], Val]]];

const primElimTypes: { [K in PrimElimName]: PrimElimTypeInfo } = {
  elimVoid: [0, ty_ => {
    const ty = force(ty_);
    if (ty.tag !== 'VNe' || ty.head.tag !== 'HPrim' || ty.head.name !== 'Void')
      return terr(`expected a Void in elimVoid`);
    return [
      VPi(many, Expl, '_', VVoid, _ => VType),
      (vmotive, vscrut) => [[], vapp(vmotive, Expl, vscrut)],
    ];
  }],
  elimUnit: [1, ty_ => {
    const ty = force(ty_);
    if (ty.tag !== 'VNe' || ty.head.tag !== 'HPrim' || ty.head.name !== '()')
      return terr(`expected a () in elimUnit`);
    return [
      VPi(many, Expl, '_', VUnitType, _ => VType),
      (vmotive, vscrut) => [[vapp(vmotive, Expl, VUnit)], vapp(vmotive, Expl, vscrut)],
    ];
  }],
  elimBool: [2, ty_ => {
    const ty = force(ty_);
    if (ty.tag !== 'VNe' || ty.head.tag !== 'HPrim' || ty.head.name !== 'Bool')
      return terr(`expected a Bool in elimBool`);
    return [
      VPi(many, Expl, '_', VBool, _ => VType),
      (vmotive, vscrut) => [[vapp(vmotive, Expl, VTrue), vapp(vmotive, Expl, VFalse)], vapp(vmotive, Expl, vscrut)],
    ];
  }],
  elimSigma: [1, (sigma_, usage) => {
    const sigma = force(sigma_);
    if (sigma.tag !== 'VSigma') return terr(`not a sigma type in elimSigma`);
    if (sigma.exclusive) return terr(`cannot call elimSigma on exclusive sigma`);
    return [
      VPi(many, Expl, '_', sigma_, _ => VType),
      (vmotive, vscrut) => [
        [VPi(multiply(usage, sigma.usage), Expl, 'x', sigma.type, x => VPi(usage, Expl, 'y', vinst(sigma, x), y => vapp(vmotive, Expl, VPair(x, y, sigma_))))],
        vapp(vmotive, Expl, vscrut),
      ],
    ];
  }],
  elimPropEq: [1, (eq_, usage) => {
    const eq = force(eq_);
    if (eq.tag !== 'VPropEq') return terr(`not a equality type in elimPropEq`);
    const A = eq.type;
    return [
      VPi(many, Expl, 'x', A, x => VPi(many, Expl, 'y', A, y => VPi(many, Expl, '_', VPropEq(A, x, y), _ => VType))),
      (vmotive, vscrut) => [
        [VPi(zero, Expl, 'x', A, x => vapp(vapp(vapp(vmotive, Expl, x), Expl, x), Expl, VRefl(A, x)))],
        vapp(vapp(vapp(vmotive, Expl, eq.left), Expl, eq.right), Expl, vscrut),
      ],
    ];
  }],
};

export const synthPrim = (name: PrimName): Val => primTypes[name].get();
export const synthPrimElim = (name: PrimElimName): PrimElimTypeInfo => primElimTypes[name];

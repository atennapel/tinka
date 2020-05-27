import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, evaluate, VDesc, VType, VFix } from './domain';
import { impossible } from './utils/utils';
import { Global } from './syntax';

const primTypes: { [K in PrimName]: () => Val } = {
  '*': () => VType,
  'Desc': () => VType,

  'End': () => VDesc,
  'Rec': () => VPi(false, '_', VDesc, _ => VDesc),
  'Arg': () => VPi(true, 't', VType, t => VPi(false, '_', VPi(false, '_', t, _ => VDesc), _ => VDesc)),

  'indDesc': () =>
    VPi(false, 'd', VDesc, d =>
    VPi(true, 'P', VPi(false, '_', VDesc, _ => VType), P =>
    VPi(false, '_', vapp(P, false, VPrim('End')), _ =>
    VPi(false, '_', VPi(false, 'r', VDesc, r => VPi(false, '_', vapp(P, false, r), _ => vapp(P, false, vapp(VPrim('Rec'), false, r)))), _ =>
    VPi(false, '_', VPi(true, 't', VType, t => VPi(false, 'f', VPi(false, '_', t, _ => VDesc), f => VPi(false, '_', VPi(false, 'x', t, x => vapp(P, false, vapp(f, false, x))), _ => vapp(P, false, vapp(vapp(VPrim('Arg'), true, t), false, f))))), _ =>
    vapp(P, false, d)))))),

  'Fix': () => VPi(false, '_', VDesc, _ => VType),
  'In': () => VPi(true, 'd', VDesc, d => VPi(false, '_', vapp(vapp(evaluate(Global('interpDesc')), false, d), false, vapp(VFix, false, d)), _ => vapp(VFix, false, d))),
  'indFix': () =>
    VPi(false, 'D', VDesc, D =>
    VPi(false, 'x', vapp(VFix, false, D), x =>
    VPi(true, 'P', VPi(false, '_', vapp(VFix, false, D), _ => VType), P =>
    VPi(false, '_', VPi(false, 'd', vapp(vapp(evaluate(Global('interpDesc')), false, D), false, vapp(VFix, false, D)), d => VPi(false, '_', vapp(vapp(vapp(vapp(evaluate(Global('AllDesc')), false, D), false, vapp(VFix, false, D)), false, P), false, d), _ => vapp(P, false, vapp(vapp(VPrim('In'), true, D), false, d)))), _ =>
    vapp(P, false, x))))),

  'unsafeCast': () => VPi(true, 'a', VType, a => VPi(true, 'b', VType, b => VPi(false, '_', b, _ => a))),
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

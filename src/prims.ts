import { PrimName } from './surface';
import { Val, VPrim, VPi, vapp, evaluate } from './domain';
import { impossible } from './utils/utils';
import { Global } from './syntax';

const Type = VPrim('*');
const Desc = VPrim('Desc');
const Fix = VPrim('Fix');

const primTypes: { [K in PrimName]: () => Val } = {
  '*': () => Type,
  'Desc': () => Type,

  'End': () => Desc,
  'Rec': () => VPi(false, '_', Desc, _ => Desc),
  'Arg': () => VPi(true, 't', Type, t => VPi(false, '_', VPi(false, '_', t, _ => Desc), _ => Desc)),

  'Fix': () => VPi(false, '_', Desc, _ => Type),
  'In': () => VPi(true, 'd', Desc, d => VPi(false, '_', vapp(vapp(evaluate(Global('interpDesc')), false, d), false, vapp(Fix, false, d)), _ => vapp(Fix, false, d))),
};

export const primType = (name: PrimName): Val => primTypes[name]() || impossible(`primType: ${name}`);

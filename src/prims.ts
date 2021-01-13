import { Expl } from './mode';
import { Name } from './names';
import { many } from './usage';
import { Lazy } from './utils/Lazy';
import { mapObj } from './utils/utils';
import { Val, VNat, VPi, VType } from './values';

export type PrimName = 'Type' | 'Nat' | 'Fin';
export const PrimNames: string[] = ['Type', 'Nat', 'Fin'];

const primTypes: { [K in PrimName]: Lazy<Val> } = mapObj({
  Type: () => VType,
  Nat: () => VType,
  Fin: () => VPi(many, Expl, '_', VNat, _ => VType),
}, Lazy.from);

export const isPrimName = (name: Name): name is PrimName => PrimNames.includes(name);

export const synthPrim = (name: PrimName): Val | null => {
  const ty = primTypes[name];
  return ty ? ty.get() || null : null;
};

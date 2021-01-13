import { Name } from './names';
import { Lazy } from './utils/Lazy';
import { mapObj } from './utils/utils';
import { Val, VType } from './values';

export type PrimName = 'Type' | 'Nat';
export const PrimNames: string[] = ['Type', 'Nat'];

const primTypes: { [K in PrimName]: Lazy<Val> } = mapObj({
  Type: () => VType,
  Nat: () => VType,
}, Lazy.from);

export const isPrimName = (name: Name): name is PrimName => PrimNames.includes(name);

export const synthPrim = (name: PrimName): Val | null => {
  const ty = primTypes[name];
  return ty ? ty.get() || null : null;
};

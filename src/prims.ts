import { Name } from './names';
import { Lazy } from './utils/Lazy';
import { mapObj } from './utils/utils';
import { Val, VType, VBool } from './values';

export type PrimName = 'Type' | 'Bool' | 'True' | 'False';
export const PrimNames: string[] = ['Type', 'Bool', 'True', 'False'];

const primTypes: { [K in PrimName]: Lazy<Val> } = mapObj({
  Type: () => VType,

  Bool: () => VType,
  True: () => VBool,
  False: () => VBool,
}, Lazy.from);

export const isPrimName = (name: Name): name is PrimName => PrimNames.includes(name);

export const synthPrim = (name: PrimName): Val | null => {
  const ty = primTypes[name];
  return ty ? ty.get() || null : null;
};

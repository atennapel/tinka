import { Val, VType, VUnitType } from './values';

export type PrimConName = '*' | '()' | 'Unit';
export type PrimElimName = never;
export type PrimName = PrimConName | PrimElimName;

export const PrimNames: string[] = ['*', '()', 'Unit'];
export const isPrimName = (x: string): x is PrimName => PrimNames.includes(x);

export const ErasedPrims = ['*', '()'];
export const isPrimErased = (name: PrimName): boolean => ErasedPrims.includes(name);

export const primType = (name: PrimName): Val => {
  if (name === '*') return VType;
  if (name === '()') return VType;
  if (name === 'Unit') return VUnitType;
  return name;
};

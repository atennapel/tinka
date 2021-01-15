import { List } from './utils/List';
import { impossible } from './utils/utils';

export type Usage = '0' | '1' | '*';
export type Subusage = '0' | '1';
export const usages: string[] = ['0', '1', '*'];

export const zero: Subusage = '0';
export const one: Subusage = '1';
export const many: Usage = '*';

export const add = (a: Usage, b: Usage): Usage => {
  if (a === many || b === many) return many;
  if (a === one) return b === one ? many : one;
  return b;
};

export const multiply = (a: Usage, b: Usage): Usage => {
  if (a === zero || b === zero) return zero;
  if (a === '1') return b;
  if (b === '1') return a;
  return many;
};

export const sub = (a: Usage, b: Usage): boolean =>
  (a === b) || ((a === zero || a === one) && b === many);

export const lub = (a: Usage, b: Usage): Usage =>
  a === b ? a : many;

export type Uses = List<Usage>;

export const noUses = (size: number): Uses =>
  List.range(size).map(() => zero);

const guardUsesZip = (a: Uses, b: Uses): void => {
  if (a.length() !== b.length()) return impossible(`trying zip Uses of different length`);
};

export const addUses = (a: Uses, b: Uses): Uses => { guardUsesZip(a, b); return a.zipWith(b, add) };
export const multiplyUses = (a: Usage, b: Uses): Uses =>
  b.map(x => multiply(a, x));

export const lubUses = (a: Uses, b: Uses): Uses => { guardUsesZip(a, b); return a.zipWith(b, lub) };

// a must not be empty
export const lubUsesAll = (a: Uses[]): Uses => a.reduce(lubUses);

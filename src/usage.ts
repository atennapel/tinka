import { List } from './utils/List';

export type Usage = '0' | '1' | '*';

export const zero: Usage = '0';
export const one: Usage = '1';
export const many: Usage = '*';

export const add = (a: Usage, b: Usage): Usage => {
  if (a === '*' || b === '*') return '*';
  if (a === '1') return b === '1' ? '*' : '1';
  return b;
};

export const multiply = (a: Usage, b: Usage): Usage => {
  if (a === '0' || b === '0') return '0';
  if (a === '1') return b;
  if (b === '1') return a;
  return '*';
};

export const sub = (a: Usage, b: Usage): boolean =>
  (a === b) || ((a === '0' || a === '1') && b === '*');

export const lub = (a: Usage, b: Usage): Usage =>
  a === b ? a : '*';

export type Uses = List<Usage>;

export const noUses = (size: number): Uses =>
  List.range(size).map(() => zero);

export const addUses = (a: Uses, b: Uses): Uses => a.zipWith(b, add);
export const multiplyUses = (a: Usage, b: Uses): Uses =>
  b.map(x => multiply(a, x));

export const lubUses = (a: Uses, b: Uses): Uses => a.zipWith(b, lub);

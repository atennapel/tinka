import { Erasure } from './mode';
import { impossible } from './utils/utils';
import { Val } from './values';

export type MetaVar = number;

export type Solution = Unsolved | Solved;
export interface Unsolved { readonly tag: 'Unsolved'; readonly type: Val; readonly erased: Erasure }
export const Unsolved = (type: Val, erased: Erasure): Unsolved => ({ tag: 'Unsolved', type, erased });
export interface Solved { readonly tag: 'Solved'; readonly solution: Val; readonly type: Val }
export const Solved = (solution: Val, type: Val): Solved => ({ tag: 'Solved', solution, type });

export type Metas = Solution[];

let metas: Metas = [];

export const resetMetas = (): void => { metas = [] };

export const freshMeta = (type: Val, erased: Erasure): MetaVar => {
  const id = metas.length;
  metas.push(Unsolved(type, erased));
  return id;
};

export const getMeta = (id: MetaVar): Solution => {
  const entry = metas[id];
  if (!entry) return impossible(`getMeta with undefined meta ${id}`);
  return entry;
};

export const setMeta = (id: MetaVar, solution: Val): void => {
  const entry = metas[id];
  if (!entry) return impossible(`setMeta with undefined meta ${id}`);
  if (entry.tag === 'Solved') return impossible(`setMeta with solved meta ${id}`);
  metas[id] = Solved(solution, entry.type);
};

export const allMetasSolved = (): boolean => metas.every(x => x.tag === 'Solved');

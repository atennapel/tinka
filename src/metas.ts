import { Val } from './domain';
import { Meta } from './syntax';
import { impossible } from './utils/utils';
import { Ix } from './names';
import { unify } from './unify';

export type Solution = Unsolved | Solved;

export type Unsolved = { tag: 'Unsolved' };
const Unsolved: Unsolved = { tag: 'Unsolved' };
export type Solved = { tag: 'Solved', val: Val };
const Solved = (val: Val): Solved => ({ tag: 'Solved', val });

let metas: Solution[] = [];
let stack: Solution[][] = [];

export type PostponedMap = { [id: number]: [Ix, Val, Val][] };
let postponed: PostponedMap = {};
let postponedStack: PostponedMap[] = [];

export const metaReset = () => { metas = []; stack = [] };
export const postponeReset = () => { postponed = {}; postponedStack = [] };

export const metaGet = (id: Ix): Solution => {
  const s = metas[id] || null;
  if (!s) return impossible(`undefined meta ?${id} in metaGet`);
  return s;
};
export const metaSet = (id: Ix, val: Val): void => {
  metas[id] = Solved(val);
};

export const freshMetaId = (): Ix => {
  const id = metas.length;
  metas[id] = Unsolved;
  return id;
};
export const freshMeta = () => Meta(freshMetaId());

export const postpone = (m: Ix, k: Ix, val1: Val, val2: Val): void => {
  postponed[m] = postponed[m] || [];
  postponed[m].push([k, val1, val2]);
};
export const getPostpones = (m: Ix): [Ix, Val, Val][] => {
  return postponed[m] || [];
};
export const getAllPostPones = (): PostponedMap => postponed;
export const getAllPostPonedFlattened = (): [Ix, Val, Val][] => {
  const r: [Ix, Val, Val][] = [];
  const m = getAllPostPones();
  for (const k in m) {
    const c = m[k];
    for (let i = 0, l = c.length; i < l; i++)
      r.push(c[i]);
  }
  return r;
};

export const tryPostponedForMeta = (m: Ix): void => {
  const all = getPostpones(m);
  postponed[m] = [];
  for (let i = 0, l = all.length; i < l; i++) {
    const c = all[i];
    unify(c[0], c[1], c[2]);
  }
};
export const tryAllPostponed = (): void => {
  const all = getAllPostPonedFlattened();
  postponed = {};
  for (let i = 0, l = all.length; i < l; i++) {
    const c = all[i];
    unify(c[0], c[1], c[2]);
  }
};

const clonePostponedMap = (obj: PostponedMap): PostponedMap => {
  const n: PostponedMap = {};
  for (const k in obj) n[k] = obj[k];
  return n;
};

export const metaPush = (): void => {
  stack.push(metas);
  postponedStack.push(postponed);
  metas = metas.slice();
  postponed = clonePostponedMap(postponed);
};
export const metaPop = (): void => {
  const x = stack.pop();
  const y = postponedStack.pop();
  if (!x || !y) return;
  metas = x;
  postponed = y;
};
export const metaDiscard = (): void => { stack.pop(); postponedStack.pop() };

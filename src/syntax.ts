import { Name, Ix, nextName } from './names';
import { Plicity } from './surface';
import { List, indecesOf, Nil, index, Cons } from './utils/list';
import * as S from './surface';
import { impossible } from './utils/utils';
import { zonk, EnvV } from './domain';

export type Term = Var | Global | App | Abs | Let | Pi | Sort | Meta | Ex | Pack | UnsafeUnpack | Unpack | UnsafeCast;

export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type Global = { tag: 'Global', name: Name };
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, name: Name, type: Term, body: Term };
export const Abs = (plicity: Plicity, name: Name, type: Term, body: Term): Abs => ({ tag: 'Abs', plicity, name, type, body });
export type Let = { tag: 'Let', plicity: Plicity, name: Name, type: Term, val: Term, body: Term };
export const Let = (plicity: Plicity, name: Name, type: Term, val: Term, body: Term): Let => ({ tag: 'Let', plicity, name, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, name, type, body });
export type Sort = { tag: 'Sort', sort: S.Sorts };
export const Sort = (sort: S.Sorts): Sort => ({ tag: 'Sort', sort });
export type Meta = { tag: 'Meta', index: Ix };
export const Meta = (index: Ix): Meta => ({ tag: 'Meta', index });
export type Ex = { tag: 'Ex', type: Term, fun: Term };
export const Ex = (type: Term, fun: Term): Ex => ({ tag: 'Ex', type, fun });
export type Pack = { tag: 'Pack', type: Term, fun: Term, hidden: Term, val: Term }
export const Pack = (type: Term, fun: Term, hidden: Term, val: Term): Pack => ({ tag: 'Pack', type, fun, hidden, val });
export type UnsafeUnpack = { tag: 'UnsafeUnpack', type: Term, fun: Term, hidden: Term, val: Term }
export const UnsafeUnpack = (type: Term, fun: Term, hidden: Term, val: Term): UnsafeUnpack => ({ tag: 'UnsafeUnpack', type, fun, hidden, val });
export type Unpack = { tag: 'Unpack', type: Term, fun: Term, hidden: Term, val: Term, elim: Term }
export const Unpack = (type: Term, fun: Term, hidden: Term, val: Term, elim: Term): Unpack => ({ tag: 'Unpack', type, fun, hidden, val, elim });
export type UnsafeCast = { tag: 'UnsafeCast', type: Term, val: Term }
export const UnsafeCast = (type: Term, val: Term): UnsafeCast => ({ tag: 'UnsafeCast', type, val });

export const Type: Sort = Sort('*');

export const showTerm = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'App') return `(${showTerm(t.left)} ${t.plicity ? '-' : ''}${showTerm(t.right)})`;
  if (t.tag === 'Abs') return `(\\(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)} = ${showTerm(t.val)} in ${showTerm(t.body)})`;
  if (t.tag === 'Pi') return `(/(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Sort') return t.sort;
  if (t.tag === 'Ex') return `(Ex ${showTerm(t.type)} ${showTerm(t.fun)})`;
  if (t.tag === 'Pack') return `(pack {${showTerm(t.type)}} {${showTerm(t.fun)}} {${showTerm(t.hidden)}} ${showTerm(t.val)})`;
  if (t.tag === 'UnsafeUnpack') return `(unsafeUnpack {${showTerm(t.type)}} {${showTerm(t.fun)}} {${showTerm(t.hidden)}} ${showTerm(t.val)})`;
  if (t.tag === 'Unpack') return `(unpack {${showTerm(t.type)}} {${showTerm(t.fun)}} {${showTerm(t.hidden)}} ${showTerm(t.val)} ${showTerm(t.elim)})`;
  if (t.tag === 'UnsafeCast') return `(unsafeUnpack ${t.type ? `{${showTerm(t.type)}} ` : ''}${showTerm(t.val)})`;
  return t;
};

export const globalUsed = (k: Name, t: Term): boolean => {
  if (t.tag === 'Global') return t.name === k;
  if (t.tag === 'App') return globalUsed(k, t.left) || globalUsed(k, t.right);
  if (t.tag === 'Abs') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Let') return globalUsed(k, t.type) || globalUsed(k, t.val) || globalUsed(k, t.body);
  if (t.tag === 'Pi') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Ex') return globalUsed(k, t.type) || globalUsed(k, t.fun);
  if (t.tag === 'Pack') return globalUsed(k, t.type) || globalUsed(k, t.fun) || globalUsed(k, t.hidden) || globalUsed(k, t.val);
  if (t.tag === 'UnsafeUnpack') return globalUsed(k, t.type) || globalUsed(k, t.fun) || globalUsed(k, t.hidden) || globalUsed(k, t.val);
  if (t.tag === 'Unpack') return globalUsed(k, t.type) || globalUsed(k, t.fun) || globalUsed(k, t.hidden) || globalUsed(k, t.val) || globalUsed(k, t.elim);
  if (t.tag === 'UnsafeCast') return globalUsed(k, t.type) || globalUsed(k, t.val);
  return false;
};
export const indexUsed = (k: Ix, t: Term): boolean => {
  if (t.tag === 'Var') return t.index === k;
  if (t.tag === 'App') return indexUsed(k, t.left) || indexUsed(k, t.right);
  if (t.tag === 'Abs') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Let') return indexUsed(k, t.type) || indexUsed(k, t.val) || indexUsed(k + 1, t.body);
  if (t.tag === 'Pi') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Ex') return indexUsed(k, t.type) || indexUsed(k, t.fun);
  if (t.tag === 'Pack') return indexUsed(k, t.type) || indexUsed(k, t.fun) || indexUsed(k, t.hidden) || indexUsed(k, t.val);
  if (t.tag === 'UnsafeUnpack') return indexUsed(k, t.type) || indexUsed(k, t.fun) || indexUsed(k, t.hidden) || indexUsed(k, t.val);
  if (t.tag === 'Unpack') return indexUsed(k, t.type) || indexUsed(k, t.fun) || indexUsed(k, t.hidden) || indexUsed(k, t.val) || indexUsed(k, t.elim);
  if (t.tag === 'UnsafeCast') return indexUsed(k, t.type) || indexUsed(k, t.val);
  return false;
};

export const isUnsolved = (t: Term): boolean => {
  if (t.tag === 'Meta') return true;
  if (t.tag === 'App') return isUnsolved(t.left) || isUnsolved(t.right);
  if (t.tag === 'Abs') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Let') return isUnsolved(t.type) || isUnsolved(t.val) || isUnsolved(t.body);
  if (t.tag === 'Pi') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Ex') return isUnsolved(t.type) || isUnsolved(t.fun);
  if (t.tag === 'Pack') return isUnsolved(t.type) || isUnsolved(t.fun) || isUnsolved(t.hidden) || isUnsolved(t.val);
  if (t.tag === 'UnsafeUnpack') return isUnsolved(t.type) || isUnsolved(t.fun) || isUnsolved(t.hidden) || isUnsolved(t.val);
  if (t.tag === 'Unpack') return isUnsolved(t.type) || isUnsolved(t.fun) || isUnsolved(t.hidden) || isUnsolved(t.val) || isUnsolved(t.elim);
  if (t.tag === 'UnsafeCast') return isUnsolved(t.type) || isUnsolved(t.val);
  return false;
};

const decideNameMany = (x: Name, t: Term[], ns: List<Name>): Name => {
  if (x === '_') return x;
  const a = indecesOf(ns, x).some(i => t.some(c => indexUsed(i + 1, c)));
  const g = t.some(c => globalUsed(x, c));
  return a || g ? decideNameMany(nextName(x), t, ns) : x;
};
const decideName = (x: Name, t: Term, ns: List<Name>): Name => decideNameMany(x, [t], ns);
export const toSurface = (t: Term, ns: List<Name> = Nil): S.Term => {
  if (t.tag === 'Var') {
    const l = index(ns, t.index);
    return l ? S.Var(l) : impossible(`var index out of range in toSurface: ${t.index}`);
  }
  if (t.tag === 'Meta') return S.Meta(t.index);
  if (t.tag === 'Sort') return S.Sort(t.sort);
  if (t.tag === 'Global') return S.Var(t.name);
  if (t.tag === 'App') return S.App(toSurface(t.left, ns), t.plicity, toSurface(t.right, ns));
  if (t.tag === 'Ex') return S.Ex(toSurface(t.type, ns), toSurface(t.fun, ns));
  if (t.tag === 'UnsafeCast') return S.UnsafeCast(toSurface(t.type, ns), toSurface(t.val, ns));
  if (t.tag === 'Pack') return S.Pack(toSurface(t.type, ns), toSurface(t.fun, ns), toSurface(t.hidden, ns), toSurface(t.val, ns));
  if (t.tag === 'UnsafeUnpack') return S.UnsafeUnpack(toSurface(t.type, ns), toSurface(t.fun, ns), toSurface(t.hidden, ns), toSurface(t.val, ns));
  if (t.tag === 'Unpack') return S.Unpack(toSurface(t.type, ns), toSurface(t.fun, ns), toSurface(t.hidden, ns), toSurface(t.val, ns), toSurface(t.elim, ns));
  if (t.tag === 'Abs') {
    const x = decideName(t.name, t.body, ns);
    return S.Abs(t.plicity, x, toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Let') {
    const x = decideName(t.name, t.body, ns);
    return S.Let(t.plicity, x, toSurface(t.type, ns), toSurface(t.val, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Pi') {
    const x = decideName(t.name, t.body, ns);
    return S.Pi(t.plicity, x, toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  return t;
};
export const showSurface = (t: Term, ns: List<Name> = Nil): string => S.showTerm(toSurface(t, ns));
export const showSurfaceZ = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): string =>
  S.showTerm(toSurface(zonk(t, vs, k, full), ns));
export const showSurfaceZErased = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): string =>
  S.showTerm(S.erase(toSurface(zonk(t, vs, k, full), ns)));

export const shift = (d: Ix, c: Ix, t: Term): Term => {
  if (t.tag === 'Var') return t.index < c ? t : Var(t.index + d);
  if (t.tag === 'Abs') return Abs(t.plicity, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'App') return App(shift(d, c, t.left), t.plicity, shift(d, c, t.right));
  if (t.tag === 'Let') return Let(t.plicity, t.name, shift(d, c, t.type), shift(d, c, t.val), shift(d, c + 1, t.body));
  if (t.tag === 'Pi') return Pi(t.plicity, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Ex') return Ex(shift(d, c, t.type), shift(d, c, t.fun));
  if (t.tag === 'UnsafeCast') return UnsafeCast(shift(d, c, t.type), shift(d, c, t.val));
  if (t.tag === 'Pack') return Pack(shift(d, c, t.type), shift(d, c, t.fun), shift(d, c, t.hidden), shift(d, c, t.val));
  if (t.tag === 'UnsafeUnpack') return UnsafeUnpack(shift(d, c, t.type), shift(d, c, t.fun), shift(d, c, t.hidden), shift(d, c, t.val));
  if (t.tag === 'Unpack') return Unpack(shift(d, c, t.type), shift(d, c, t.fun), shift(d, c, t.hidden), shift(d, c, t.val), shift(d, c, t.elim));
  return t;
};

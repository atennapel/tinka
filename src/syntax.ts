import { Name, Ix, nextName } from './names';
import { Plicity } from './surface';
import { List, indecesOf, Nil, index, Cons } from './utils/list';
import * as S from './surface';
import { impossible } from './utils/util';
import { zonk, EnvV } from './domain';

export type Term = Var | Global | App | Abs | Let | Pi | Type | Ann | Hole | Meta;

export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type Global = { tag: 'Global', name: Name };
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, name: Name, type: Term | null, body: Term };
export const Abs = (plicity: Plicity, name: Name, type: Term | null, body: Term): Abs => ({ tag: 'Abs', plicity, name, type, body });
export type Let = { tag: 'Let', plicity: Plicity, name: Name, type: Term | null, val: Term, body: Term };
export const Let = (plicity: Plicity, name: Name, type: Term | null, val: Term, body: Term): Let => ({ tag: 'Let', plicity, name, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, rec: Name, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, rec: Name, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, rec, name, type, body });
export type Type = { tag: 'Type' };
export const Type: Type = { tag: 'Type' };
export type Ann = { tag: 'Ann', term: Term, type: Term };
export const Ann = (term: Term, type: Term): Ann => ({ tag: 'Ann', term, type });
export type Hole = { tag: 'Hole', name: Name | null };
export const Hole = (name: Name | null = null): Hole => ({ tag: 'Hole', name });
export type Meta = { tag: 'Meta', index: Ix };
export const Meta = (index: Ix): Meta => ({ tag: 'Meta', index });

export const showTerm = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'App') return `(${showTerm(t.left)} ${t.plicity ? '-' : ''}${showTerm(t.right)})`;
  if (t.tag === 'Abs')
    return t.type ? `(\\(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})` : `(\\${t.plicity ? '-' : ''}${t.name}. ${showTerm(t.body)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${t.name}${t.type ? ` : ${showTerm(t.type)}` : ''} = ${showTerm(t.val)} in ${showTerm(t.body)})`;
  if (t.tag === 'Pi') return `(/(${t.rec} @ ${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Type') return '*';
  if (t.tag === 'Ann') return `(${showTerm(t.term)} : ${showTerm(t.type)})`;
  if (t.tag === 'Hole') return `_${t.name || ''}`;
  return t;
};

export const globalUsed = (k: Name, t: Term): boolean => {
  if (t.tag === 'Global') return t.name === k;
  if (t.tag === 'App') return globalUsed(k, t.left) || globalUsed(k, t.right);
  if (t.tag === 'Abs') return (t.type && globalUsed(k, t.type)) || globalUsed(k, t.body);
  if (t.tag === 'Let') return (t.type && globalUsed(k, t.type)) || globalUsed(k, t.val) || globalUsed(k, t.body);
  if (t.tag === 'Pi') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Ann') return globalUsed(k, t.term) || globalUsed(k, t.type);
  return false;
};
export const indexUsed = (k: Ix, t: Term): boolean => {
  if (t.tag === 'Var') return t.index === k;
  if (t.tag === 'App') return indexUsed(k, t.left) || indexUsed(k, t.right);
  if (t.tag === 'Abs') return (t.type && indexUsed(k, t.type)) || indexUsed(k + 1, t.body);
  if (t.tag === 'Let') return (t.type && indexUsed(k, t.type)) || indexUsed(k, t.val) || indexUsed(k + 1, t.body);
  if (t.tag === 'Pi') return indexUsed(k, t.type) || indexUsed(k + 2, t.body);
  if (t.tag === 'Ann') return indexUsed(k, t.term) || indexUsed(k, t.type);
 return false;
};

export const isUnsolved = (t: Term): boolean => {
  if (t.tag === 'Hole') return true;
  if (t.tag === 'Meta') return true;
  if (t.tag === 'App') return isUnsolved(t.left) || isUnsolved(t.right);
  if (t.tag === 'Abs') return (t.type && isUnsolved(t.type)) || isUnsolved(t.body);
  if (t.tag === 'Let') return (t.type && isUnsolved(t.type)) || isUnsolved(t.val) || isUnsolved(t.body);
  if (t.tag === 'Pi') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Ann') return isUnsolved(t.term) || isUnsolved(t.type);
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
  if (t.tag === 'Type') return S.Type;
  if (t.tag === 'Global') return S.Var(t.name);
  if (t.tag === 'App') return S.App(toSurface(t.left, ns), t.plicity, toSurface(t.right, ns));
  if (t.tag === 'Ann') return S.Ann(toSurface(t.term, ns), toSurface(t.type, ns));
  if (t.tag === 'Hole') return S.Hole(t.name);
  if (t.tag === 'Abs') {
    const x = decideName(t.name, t.body, ns);
    return S.Abs(t.plicity, x, t.type && toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Let') {
    const x = decideName(t.name, t.body, ns);
    return S.Let(t.plicity, x, t.type && toSurface(t.type, ns), toSurface(t.val, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Pi') {
    const x = decideName(t.rec, t.body, ns);
    const y = decideName(t.name, t.body, ns);
    return S.Pi(t.plicity, x, y, toSurface(t.type, ns), toSurface(t.body, Cons(y, Cons(x, ns))));
  }
  return t;
};
export const showSurface = (t: Term, ns: List<Name> = Nil): string => S.showTerm(toSurface(t, ns));
export const showSurfaceZ = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: number = 0): string =>
  S.showTerm(toSurface(zonk(t, vs, k, full), ns));

export const shift = (d: Ix, c: Ix, t: Term): Term => {
  if (t.tag === 'Var') return t.index < c ? t : Var(t.index + d);
  if (t.tag === 'Abs') return Abs(t.plicity, t.name, t.type && shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'App') return App(shift(d, c, t.left), t.plicity, shift(d, c, t.right));
  if (t.tag === 'Let') return Let(t.plicity, t.name, t.type && shift(d, c, t.type), shift(d, c, t.val), shift(d, c + 1, t.body));
  if (t.tag === 'Pi') return Pi(t.plicity, t.rec, t.name, shift(d, c, t.type), shift(d, c + 2, t.body));
  if (t.tag === 'Ann') return Ann(shift(d, c, t.term), shift(d, c, t.type));
  return t;
};

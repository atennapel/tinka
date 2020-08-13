import { Name, Ix, nextName } from './names';
import { Plicity } from './surface';
import { List, indecesOf, Nil, index, Cons } from './utils/list';
import * as S from './surface';
import { impossible } from './utils/utils';
import { zonk, EnvV } from './domain';

export type Term = Var | Global | App | Abs | Pair | Proj | Let | Pi | Sigma | Data | TCon | Type | Prim | Meta;

export type Prim = { tag: 'Prim', name: S.PrimName };
export const Prim = (name: S.PrimName): Prim => ({ tag: 'Prim', name });
export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type Global = { tag: 'Global', name: Name };
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, name: Name, type: Term, body: Term };
export const Abs = (plicity: Plicity, name: Name, type: Term, body: Term): Abs => ({ tag: 'Abs', plicity, name, type, body });
export type Pair = { tag: 'Pair', plicity: Plicity, plicity2: Plicity, fst: Term, snd: Term, type: Term };
export const Pair = (plicity: Plicity, plicity2: Plicity, fst: Term, snd: Term, type: Term): Pair => ({ tag: 'Pair', plicity, plicity2, fst, snd, type });
export type Proj = { tag: 'Proj', proj: 'fst' | 'snd', term: Term };
export const Proj = (proj: 'fst' | 'snd', term: Term): Proj => ({ tag: 'Proj', proj, term });
export type Let = { tag: 'Let', plicity: Plicity, name: Name, type: Term, val: Term, body: Term };
export const Let = (plicity: Plicity, name: Name, type: Term, val: Term, body: Term): Let => ({ tag: 'Let', plicity, name, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, name, type, body });
export type Sigma = { tag: 'Sigma', plicity: Plicity, plicity2: Plicity, name: Name, type: Term, body: Term };
export const Sigma = (plicity: Plicity, plicity2: Plicity, name: Name, type: Term, body: Term): Sigma => ({ tag: 'Sigma', plicity, plicity2, name, type, body });
export type Data = { tag: 'Data', index: Term, cons: Term[] };
export const Data = (index: Term, cons: Term[]): Data => ({ tag: 'Data', index, cons });
export type TCon = { tag: 'TCon', data: Term, arg: Term };
export const TCon = (data: Term, arg: Term): TCon => ({ tag: 'TCon', data, arg });
export type Type = { tag: 'Type' };
export const Type: Type = { tag: 'Type' };
export type Meta = { tag: 'Meta', index: Ix };
export const Meta = (index: Ix): Meta => ({ tag: 'Meta', index });

export const showTerm = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Meta') return `?${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'Type') return '*';
  if (t.tag === 'Prim') return `%${t.name}`;
  if (t.tag === 'App') return `(${showTerm(t.left)} ${t.plicity ? '-' : ''}${showTerm(t.right)})`;
  if (t.tag === 'Abs') return `(\\(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Pair') return `(${t.plicity ? '{' : ''}${showTerm(t.fst)}${t.plicity ? '}' : ''}, ${t.plicity ? '{' : ''}${showTerm(t.snd)}${t.plicity ? '}' : ''} : ${showTerm(t.type)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)} = ${showTerm(t.val)} in ${showTerm(t.body)})`;
  if (t.tag === 'Pi') return `(/(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Sigma') return `((${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}) ** ${t.plicity ? '-' : ''}${showTerm(t.body)})`;
  if (t.tag === 'Proj') return `(${t.proj} ${showTerm(t.term)})`;
  if (t.tag === 'Data') return `(data ${showTerm(t.index)}. ${t.cons.map(t => showTerm(t)).join(' ')})`;
  if (t.tag === 'TCon') return `(tcon ${showTerm(t.data)} ${showTerm(t.arg)})`;
  return t;
};

export const globalUsed = (k: Name, t: Term): boolean => {
  if (t.tag === 'Global') return t.name === k;
  if (t.tag === 'App') return globalUsed(k, t.left) || globalUsed(k, t.right);
  if (t.tag === 'Proj') return globalUsed(k, t.term);
  if (t.tag === 'Pair') return globalUsed(k, t.fst) || globalUsed(k, t.snd) || globalUsed(k, t.type);
  if (t.tag === 'Abs') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Let') return globalUsed(k, t.type) || globalUsed(k, t.val) || globalUsed(k, t.body);
  if (t.tag === 'Pi') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Sigma') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Data') return globalUsed(k, t.index) || t.cons.some(x => globalUsed(k, x));
  if (t.tag === 'TCon') return globalUsed(k, t.data) || globalUsed(k, t.arg);
  return false;
};
export const indexUsed = (k: Ix, t: Term): boolean => {
  if (t.tag === 'Var') return t.index === k;
  if (t.tag === 'App') return indexUsed(k, t.left) || indexUsed(k, t.right);
  if (t.tag === 'Pair') return indexUsed(k, t.fst) || indexUsed(k, t.snd) || indexUsed(k, t.type);
  if (t.tag === 'Abs') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Let') return indexUsed(k, t.type) || indexUsed(k, t.val) || indexUsed(k + 1, t.body);
  if (t.tag === 'Pi') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Sigma') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Proj') return indexUsed(k, t.term);
  if (t.tag === 'Data') return indexUsed(k, t.index) || t.cons.some(x => indexUsed(k, x));
  if (t.tag === 'TCon') return indexUsed(k, t.data) || indexUsed(k, t.arg);
  return false;
};

export const isUnsolved = (t: Term): boolean => {
  if (t.tag === 'Meta') return true;
  if (t.tag === 'App') return isUnsolved(t.left) || isUnsolved(t.right);
  if (t.tag === 'Pair') return isUnsolved(t.fst) || isUnsolved(t.snd) || isUnsolved(t.type);
  if (t.tag === 'Abs') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Let') return isUnsolved(t.type) || isUnsolved(t.val) || isUnsolved(t.body);
  if (t.tag === 'Pi') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Sigma') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Proj') return isUnsolved(t.term);
  if (t.tag === 'Data') return isUnsolved(t.index) || t.cons.some(x => isUnsolved(x));
  if (t.tag === 'TCon') return isUnsolved(t.data) || isUnsolved(t.arg);
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
  if (t.tag === 'Global') return S.Var(t.name);
  if (t.tag === 'Prim') return S.Prim(t.name);
  if (t.tag === 'Type') return S.Type;
  if (t.tag === 'App') return S.App(toSurface(t.left, ns), t.plicity, toSurface(t.right, ns));
  if (t.tag === 'Pair') return S.Ann(S.Pair(t.plicity, t.plicity2, toSurface(t.fst, ns), toSurface(t.snd, ns)), toSurface(t.type, ns));
  if (t.tag === 'Proj') return S.Proj(S.PCore(t.proj), toSurface(t.term, ns));
  if (t.tag === 'Data') return S.Data(toSurface(t.index, ns), t.cons.map(x => toSurface(x, ns)));
  if (t.tag === 'TCon') return S.TCon(toSurface(t.data, ns), toSurface(t.arg, ns));
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
  if (t.tag === 'Sigma') {
    const x = decideName(t.name, t.body, ns);
    return S.Sigma(t.plicity, t.plicity2, x, toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  return t;
};
export const showSurface = (t: Term, ns: List<Name> = Nil): string => S.showTerm(toSurface(t, ns));
export const showSurfaceZ = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): string =>
  S.showTerm(toSurface(zonk(t, vs, k, full), ns));
export const showSurfaceZErased = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): string =>
  S.showTerm(S.erase(toSurface(zonk(t, vs, k, full), ns)));

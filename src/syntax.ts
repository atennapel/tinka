import { Name, Ix, nextName } from './names';
import { Plicity, DescConTag } from './surface';
import { List, indecesOf, Nil, index, Cons } from './utils/list';
import * as S from './surface';
import { impossible } from './utils/utils';
import { zonk, EnvV } from './domain';

export type Term = Var | Global | App | Abs | Pair | Fst | Snd | EnumInd | Elem | Let | Enum | Pi | Sigma | Sort | Meta | UnsafeCast | Desc | DescCon;

export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type Global = { tag: 'Global', name: Name };
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, name: Name, type: Term, body: Term };
export const Abs = (plicity: Plicity, name: Name, type: Term, body: Term): Abs => ({ tag: 'Abs', plicity, name, type, body });
export type Pair = { tag: 'Pair', fst: Term, snd: Term, type: Term };
export const Pair = (fst: Term, snd: Term, type: Term): Pair => ({ tag: 'Pair', fst, snd, type });
export type Fst = { tag: 'Fst', term: Term };
export const Fst = (term: Term): Fst => ({ tag: 'Fst', term });
export type Snd = { tag: 'Snd', term: Term };
export const Snd = (term: Term): Snd => ({ tag: 'Snd', term });
export type Let = { tag: 'Let', plicity: Plicity, name: Name, type: Term, val: Term, body: Term };
export const Let = (plicity: Plicity, name: Name, type: Term, val: Term, body: Term): Let => ({ tag: 'Let', plicity, name, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, name, type, body });
export type Sigma = { tag: 'Sigma', name: Name, type: Term, body: Term };
export const Sigma = (name: Name, type: Term, body: Term): Sigma => ({ tag: 'Sigma', name, type, body });
export type Enum = { tag: 'Enum', num: number };
export const Enum = (num: number): Enum => ({ tag: 'Enum', num });
export type Elem = { tag: 'Elem', num: number, total: number };
export const Elem = (num: number, total: number): Elem => ({ tag: 'Elem', num, total });
export type EnumInd = { tag: 'EnumInd', num: number, prop: Term, term: Term, args: Term[] };
export const EnumInd = (num: number, prop: Term, term: Term, args: Term[]): EnumInd => ({ tag: 'EnumInd', num, prop, term, args });
export type Sort = { tag: 'Sort', sort: S.Sorts };
export const Sort = (sort: S.Sorts): Sort => ({ tag: 'Sort', sort });
export type Meta = { tag: 'Meta', index: Ix };
export const Meta = (index: Ix): Meta => ({ tag: 'Meta', index });
export type UnsafeCast = { tag: 'UnsafeCast', type: Term, val: Term }
export const UnsafeCast = (type: Term, val: Term): UnsafeCast => ({ tag: 'UnsafeCast', type, val });

export type Desc = { tag: 'Desc' };
export const Desc: Desc = { tag: 'Desc' };
export type DescCon = { tag: 'DescCon', con: DescConTag, args: Term[] };
export const DescCon = (con: DescConTag, args: Term[]): DescCon => ({ tag: 'DescCon', con, args });

export const Type: Sort = Sort('*');

export const showTerm = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Meta') return `??${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'Desc') return `Desc`;
  if (t.tag === 'Enum') return `#${t.num}`;
  if (t.tag === 'Elem') return `@${t.num}/${t.total}`;
  if (t.tag === 'App') return `(${showTerm(t.left)} ${t.plicity ? '-' : ''}${showTerm(t.right)})`;
  if (t.tag === 'Abs') return `(\\(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Pair') return `(${showTerm(t.fst)}, ${showTerm(t.snd)} : ${showTerm(t.type)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)} = ${showTerm(t.val)} in ${showTerm(t.body)})`;
  if (t.tag === 'Pi') return `(/(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Sigma') return `((${t.name} : ${showTerm(t.type)}) ** ${showTerm(t.body)})`;
  if (t.tag === 'Sort') return t.sort;
  if (t.tag === 'UnsafeCast') return `(unsafeCast ${t.type ? `{${showTerm(t.type)}} ` : ''}${showTerm(t.val)})`;
  if (t.tag === 'Fst') return `(fst ${showTerm(t.term)})`;
  if (t.tag === 'Snd') return `(snd ${showTerm(t.term)})`;
  if (t.tag === 'EnumInd') return `(?${t.num} {${showTerm(t.prop)}} ${showTerm(t.term)}${t.args.length > 0 ? ` ${t.args.map(showTerm).join(' ')}` : ''})`;
  if (t.tag === 'DescCon') return `(condesc ${t.con}${t.args.length > 0 ? ` ${t.args.map(showTerm).join(' ')}` : ''})`;
  return t;
};

export const globalUsed = (k: Name, t: Term): boolean => {
  if (t.tag === 'Global') return t.name === k;
  if (t.tag === 'App') return globalUsed(k, t.left) || globalUsed(k, t.right);
  if (t.tag === 'Fst') return globalUsed(k, t.term);
  if (t.tag === 'Snd') return globalUsed(k, t.term);
  if (t.tag === 'Pair') return globalUsed(k, t.fst) || globalUsed(k, t.snd) || globalUsed(k, t.type);
  if (t.tag === 'Abs') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Let') return globalUsed(k, t.type) || globalUsed(k, t.val) || globalUsed(k, t.body);
  if (t.tag === 'Pi') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Sigma') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'UnsafeCast') return globalUsed(k, t.type) || globalUsed(k, t.val);
  if (t.tag === 'EnumInd') return globalUsed(k, t.prop) || globalUsed(k, t.term) || t.args.some(x => globalUsed(k, x));
  if (t.tag === 'DescCon') return t.args.some(x => globalUsed(k, x));
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
  if (t.tag === 'UnsafeCast') return indexUsed(k, t.type) || indexUsed(k, t.val);
  if (t.tag === 'Fst') return indexUsed(k, t.term);
  if (t.tag === 'Snd') return indexUsed(k, t.term);
  if (t.tag === 'EnumInd') return indexUsed(k, t.prop) || indexUsed(k, t.term) || t.args.some(x => indexUsed(k, x));
  if (t.tag === 'DescCon') return t.args.some(x => indexUsed(k, x));
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
  if (t.tag === 'UnsafeCast') return isUnsolved(t.type) || isUnsolved(t.val);
  if (t.tag === 'Fst') return isUnsolved(t.term);
  if (t.tag === 'Snd') return isUnsolved(t.term);
  if (t.tag === 'EnumInd') return isUnsolved(t.prop) || isUnsolved(t.term) || t.args.some(x => isUnsolved(x));
  if (t.tag === 'DescCon') return t.args.some(x => isUnsolved(x));
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
  if (t.tag === 'Enum') return S.Enum(t.num);
  if (t.tag === 'Elem') return S.Elem(t.num, t.total);
  if (t.tag === 'Desc') return S.Desc;
  if (t.tag === 'App') return S.App(toSurface(t.left, ns), t.plicity, toSurface(t.right, ns));
  if (t.tag === 'Pair') return S.Ann(S.Pair(toSurface(t.fst, ns), toSurface(t.snd, ns)), toSurface(t.type, ns));
  if (t.tag === 'UnsafeCast') return S.UnsafeCast(toSurface(t.type, ns), toSurface(t.val, ns));
  if (t.tag === 'Fst') return S.Fst(toSurface(t.term, ns));
  if (t.tag === 'Snd') return S.Snd(toSurface(t.term, ns));
  if (t.tag === 'EnumInd') return S.EnumInd(t.num, toSurface(t.prop, ns), toSurface(t.term, ns), t.args.map(x => toSurface(x, ns)));
  if (t.tag === 'DescCon') return S.DescCon(t.con, t.args.map(x => toSurface(x, ns)));
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
    return S.Sigma(x, toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  return t;
};
export const showSurface = (t: Term, ns: List<Name> = Nil): string => S.showTerm(toSurface(t, ns));
export const showSurfaceZ = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): string =>
  S.showTerm(toSurface(zonk(t, vs, k, full), ns));
export const showSurfaceZErased = (t: Term, ns: List<Name> = Nil, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): string =>
  S.showTerm(S.erase(toSurface(zonk(t, vs, k, full), ns)));

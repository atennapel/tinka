import { Name, Ix, nextName } from './names';
import { Plicity } from './surface';
import { List, indecesOf, Nil, index, Cons } from './utils/list';
import * as S from './surface';
import { impossible } from './utils/util';
import { zonk, EnvV } from './domain';

export type Term = Var | Global | App | Abs | Let | Roll | Unroll | Con | Case | Pi | Fix | Data | Type | Ann | Hole | Meta;

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
export type Roll = { tag: 'Roll', type: Term | null, term: Term };
export const Roll = (type: Term | null, term: Term): Roll => ({ tag: 'Roll', type, term });
export type Unroll = { tag: 'Unroll', term: Term };
export const Unroll = (term: Term): Unroll => ({ tag: 'Unroll', term });
export type Con = { tag: 'Con', type: Term | null, index: Ix, total: number, args: [Term, Plicity][] };
export const Con = (type: Term | null, index: Ix, total: number, args: [Term, Plicity][]): Con => ({ tag: 'Con', type, index, total, args });
export type Case = { tag: 'Case', type: Term, prop: Term, scrut: Term, cases: Term[] };
export const Case = (type: Term, prop: Term, scrut: Term, cases: Term[]): Case => ({ tag: 'Case', type, prop, scrut, cases });
export type Pi = { tag: 'Pi', plicity: Plicity, name: Name, type: Term, body: Term };
export const Pi = (plicity: Plicity, name: Name, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, name, type, body });
export type Fix = { tag: 'Fix', name: Name, type: Term, body: Term };
export const Fix = (name: Name, type: Term, body: Term): Fix => ({ tag: 'Fix', name, type, body });
export type Data = { tag: 'Data', name: Name, cons: Term[] };
export const Data = (name: Name, cons: Term[]): Data => ({ tag: 'Data', name, cons });
export type Type = { tag: 'Type' };
export const Type: Type = { tag: 'Type' };
export type Desc = { tag: 'Desc' };
export const Desc: Desc = { tag: 'Desc' };
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
  if (t.tag === 'Roll') return t.type ? `(roll {${showTerm(t.type)}} ${showTerm(t.term)})` : `(roll ${showTerm(t.term)})`;
  if (t.tag === 'Unroll') return `(unroll ${showTerm(t.term)})`;
  if (t.tag === 'Con') return `(con ${t.type ? `{${showTerm(t.type)}} ` : ''}${t.index} ${t.total}${t.args.length > 0 ? ' ' : ''}${t.args.map(([t, p]) => p ? `{${showTerm(t)}}` : showTerm(t)).join(' ')})`;
  if (t.tag === 'Case') return `(case {${showTerm(t.type)}} {${showTerm(t.prop)}} ${showTerm(t.scrut)}${t.cases.length > 0 ? ' ' : ''}${t.cases.map(t => showTerm(t)).join(' ')})`;
  if (t.tag === 'Pi') return `(/(${t.plicity ? '-' : ''}${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Fix') return `(fix (${t.name} : ${showTerm(t.type)}). ${showTerm(t.body)})`;
  if (t.tag === 'Data') return `(data ${t.name}. ${t.cons.map(showTerm).join(' | ')})`;
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
  if (t.tag === 'Roll') return (t.type && globalUsed(k, t.type)) || globalUsed(k, t.term)
  if (t.tag === 'Unroll') return globalUsed(k, t.term);
  if (t.tag === 'Pi') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Fix') return globalUsed(k, t.type) || globalUsed(k, t.body);
  if (t.tag === 'Data') return t.cons.some(x => globalUsed(k, x));
  if (t.tag === 'Ann') return globalUsed(k, t.term) || globalUsed(k, t.type);
  if (t.tag === 'Con') return (t.type && globalUsed(k, t.type)) || t.args.some(([x, _]) => globalUsed(k, x));
  if (t.tag === 'Case') return globalUsed(k, t.type) || globalUsed(k, t.prop) || globalUsed(k, t.scrut) || t.cases.some(x => globalUsed(k, x));
  return false;
};
export const indexUsed = (k: Ix, t: Term): boolean => {
  if (t.tag === 'Var') return t.index === k;
  if (t.tag === 'App') return indexUsed(k, t.left) || indexUsed(k, t.right);
  if (t.tag === 'Abs') return (t.type && indexUsed(k, t.type)) || indexUsed(k + 1, t.body);
  if (t.tag === 'Let') return (t.type && indexUsed(k, t.type)) || indexUsed(k, t.val) || indexUsed(k + 1, t.body);
  if (t.tag === 'Roll') return (t.type && indexUsed(k, t.type)) || indexUsed(k, t.term);
  if (t.tag === 'Unroll') return indexUsed(k, t.term);
  if (t.tag === 'Pi') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Fix') return indexUsed(k, t.type) || indexUsed(k + 1, t.body);
  if (t.tag === 'Data') return t.cons.some(x => indexUsed(k + 1, x));
  if (t.tag === 'Ann') return indexUsed(k, t.term) || indexUsed(k, t.type);
  if (t.tag === 'Con') return (t.type && indexUsed(k, t.type)) || t.args.some(([x, _]) => indexUsed(k, x));
  if (t.tag === 'Case') return indexUsed(k, t.type) || indexUsed(k, t.prop) || indexUsed(k, t.scrut) || t.cases.some(x => indexUsed(k, x));
  return false;
};

export const isUnsolved = (t: Term): boolean => {
  if (t.tag === 'Hole') return true;
  if (t.tag === 'Meta') return true;
  if (t.tag === 'App') return isUnsolved(t.left) || isUnsolved(t.right);
  if (t.tag === 'Abs') return (t.type && isUnsolved(t.type)) || isUnsolved(t.body);
  if (t.tag === 'Let') return (t.type && isUnsolved(t.type)) || isUnsolved(t.val) || isUnsolved(t.body);
  if (t.tag === 'Roll') return (t.type && isUnsolved(t.type)) || isUnsolved(t.term);
  if (t.tag === 'Unroll') return isUnsolved(t.term);
  if (t.tag === 'Pi') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Fix') return isUnsolved(t.type) || isUnsolved(t.body);
  if (t.tag === 'Data') return t.cons.some(isUnsolved);
  if (t.tag === 'Ann') return isUnsolved(t.term) || isUnsolved(t.type);
  if (t.tag === 'Con') return (t.type && isUnsolved(t.type)) || t.args.some(([x, _]) => isUnsolved(x));
  if (t.tag === 'Case') return isUnsolved(t.type) || isUnsolved(t.prop) || isUnsolved(t.scrut) || t.cases.some(x => isUnsolved(x));
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
  if (t.tag === 'Unroll') return S.Unroll(toSurface(t.term, ns));
  if (t.tag === 'Con') return S.Con(t.type && toSurface(t.type, ns), t.index, t.total, t.args.map(([x, p]) => [toSurface(x, ns), p]));
  if (t.tag === 'Case') return S.Case(toSurface(t.type, ns), toSurface(t.prop, ns), toSurface(t.scrut, ns), t.cases.map(x => toSurface(x, ns)));
  if (t.tag === 'Roll') return S.Roll(t.type && toSurface(t.type, ns), toSurface(t.term, ns));
  if (t.tag === 'Abs') {
    const x = decideName(t.name, t.body, ns);
    return S.Abs(t.plicity, x, t.type && toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Let') {
    const x = decideName(t.name, t.body, ns);
    return S.Let(t.plicity, x, t.type && toSurface(t.type, ns), toSurface(t.val, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Pi') {
    const x = decideName(t.name, t.body, ns);
    return S.Pi(t.plicity, x, toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Fix') {
    const x = decideName(t.name, t.body, ns);
    return S.Fix(x, toSurface(t.type, ns), toSurface(t.body, Cons(x, ns)));
  }
  if (t.tag === 'Data') {
    const x = decideNameMany(t.name, t.cons, ns);
    return S.Data(x, t.cons.map(c => toSurface(c, Cons(x, ns))));
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
  if (t.tag === 'Roll') return Roll(t.type && shift(d, c, t.type), shift(d, c, t.term));
  if (t.tag === 'Unroll') return Unroll(shift(d, c, t.term));
  if (t.tag === 'Pi') return Pi(t.plicity, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Fix') return Fix(t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Data') return Data(t.name, t.cons.map(x => shift(d, c + 1, x)));
  if (t.tag === 'Ann') return Ann(shift(d, c, t.term), shift(d, c, t.type));
  if (t.tag === 'Con') return Con(t.type && shift(d, c, t.type), t.index, t.total, t.args.map(([x, p]) => [shift(d, c, x), p]));
  if (t.tag === 'Case') return Case(shift(d, c, t.type), shift(d, c, t.prop), shift(d, c, t.scrut), t.cases.map(x => shift(d, c, x)));
  return t;
};

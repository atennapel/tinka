import { Ix, Name } from '../names';
import { Plicity } from '../surface';
import * as S from '../surface';
import { Nil, List, lookup, Cons } from '../utils/list';
import { impossible } from '../utils/util';
import { Term as ITerm } from '../syntax';

export type Term = Var | Global | App | Abs | Let | Pi | Type;

export type Var = { tag: 'Var', index: Ix };
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export type Global = { tag: 'Global', name: Name };
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export type App = { tag: 'App', left: Term, plicity: Plicity, right: Term };
export const App = (left: Term, plicity: Plicity, right: Term): App => ({ tag: 'App', left, plicity, right });
export type Abs = { tag: 'Abs', plicity: Plicity, type: Term, body: Term };
export const Abs = (plicity: Plicity, type: Term, body: Term): Abs => ({ tag: 'Abs', plicity, type, body });
export type Let = { tag: 'Let', plicity: Plicity, type: Term, val: Term, body: Term };
export const Let = (plicity: Plicity, type: Term, val: Term, body: Term): Let => ({ tag: 'Let', plicity, type, val, body });
export type Pi = { tag: 'Pi', plicity: Plicity, type: Term, body: Term };
export const Pi = (plicity: Plicity, type: Term, body: Term): Pi => ({ tag: 'Pi', plicity, type, body });
export type Type = { tag: 'Type' };
export const Type: Type = { tag: 'Type' };

export const showTerm = (t: Term): string => {
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Global') return t.name;
  if (t.tag === 'App') return `(${showTerm(t.left)} ${t.plicity ? '-' : ''}${showTerm(t.right)})`;
  if (t.tag === 'Abs') return `(\\${t.plicity ? '-' : ''}${showTerm(t.type)}. ${showTerm(t.body)})`;
  if (t.tag === 'Let') return `(let ${t.plicity ? '-' : ''}${showTerm(t.type)} = ${showTerm(t.val)} in ${showTerm(t.body)})`;
  if (t.tag === 'Pi') return `(/${t.plicity ? '-' : ''}${showTerm(t.type)}. ${showTerm(t.body)})`;
  if (t.tag === 'Type') return '*';
  return t;
};

export const fromSurface = (t: S.Term, ns: List<[Name, Ix]> = Nil, k: Ix = 0): Term => {
  if (t.tag === 'Var') {
    const l = lookup(ns, t.name);
    return l === null ? Global(t.name) : Var(k - l - 1);
  }
  if (t.tag === 'App') return App(fromSurface(t.left, ns, k), t.plicity, fromSurface(t.right, ns, k));
  if (t.tag === 'Abs' && t.type) return Abs(t.plicity, fromSurface(t.type, ns, k), fromSurface(t.body, Cons([t.name, k], ns), k + 1));
  if (t.tag === 'Let' && t.type) return Let(t.plicity, fromSurface(t.type, ns, k), fromSurface(t.val, ns, k), fromSurface(t.body, Cons([t.name, k], ns), k + 1));
  if (t.tag === 'Pi') return Pi(t.plicity, fromSurface(t.type, ns, k), fromSurface(t.body, Cons([t.name, k], ns), k + 1));
  if (t.tag === 'Type') return Type;
  return impossible(`fromSurface: ${t.tag}`);
};

export const toCore = (t: ITerm): Term => {
  if (t.tag === 'Type') return Type;
  if (t.tag === 'Var') return Var(t.index);
  if (t.tag === 'Global') return Global(t.name);
  if (t.tag === 'App') return App(toCore(t.left), t.plicity, toCore(t.right));
  if (t.tag === 'Pi') return Pi(t.plicity, toCore(t.type), toCore(t.body));
  if (t.tag === 'Let' && t.type) return Let(t.plicity, toCore(t.type), toCore(t.val), toCore(t.body));
  if (t.tag === 'Abs' && t.type) return Abs(t.plicity, toCore(t.type), toCore(t.body));
  return impossible(`toCore: ${t.tag}`);
};

export const shift = (d: Ix, c: Ix, t: Term): Term => {
  if (t.tag === 'Var') return t.index < c ? t : Var(t.index + d);
  if (t.tag === 'Abs') return Abs(t.plicity, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'App') return App(shift(d, c, t.left), t.plicity, shift(d, c, t.right));
  if (t.tag === 'Let') return Let(t.plicity, shift(d, c, t.val), shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Pi') return Pi(t.plicity, shift(d, c, t.type), shift(d, c + 1, t.body));
  return t;
};

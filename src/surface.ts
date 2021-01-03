import { Core } from './core';
import { Mode } from './mode';
import { chooseName, Lvl, Name } from './names';
import { many, Usage } from './usage';
import { cons, List, nil } from './utils/List';
import { impossible } from './utils/utils';
import { quote, Val } from './values';

export type Surface =
  Var | Let |
  Type |
  Pi | Abs | App |
  Sigma | Pair | IndSigma;

export interface Var { readonly tag: 'Var'; readonly name: Name }
export const Var = (name: Name): Var => ({ tag: 'Var', name });
export interface Let { readonly tag: 'Let'; readonly usage: Usage; readonly name: Name; readonly type: Surface | null; readonly val: Surface; readonly body: Surface }
export const Let = (usage: Usage, name: Name, type: Surface | null, val: Surface, body: Surface): Let => ({ tag: 'Let', usage, name, type, val, body });
export interface Type { readonly tag: 'Type' }
export const Type: Type = { tag: 'Type' };
export interface Pi { readonly tag: 'Pi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Surface; readonly body: Surface }
export const Pi = (usage: Usage, mode: Mode, name: Name, type: Surface, body: Surface): Pi =>
  ({ tag: 'Pi', usage, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Surface | null; readonly body: Surface }
export const Abs = (usage: Usage, mode: Mode, name: Name, type: Surface | null, body: Surface): Abs =>
  ({ tag: 'Abs', usage, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Surface; readonly mode: Mode; readonly arg: Surface }
export const App = (fn: Surface, mode: Mode, arg: Surface): App => ({ tag: 'App', fn, mode, arg });
export interface Sigma { readonly tag: 'Sigma'; readonly usage: Usage; readonly name: Name; readonly type: Surface; readonly body: Surface }
export const Sigma = (usage: Usage, name: Name, type: Surface, body: Surface): Sigma => ({ tag: 'Sigma', usage, name, type, body });
export interface Pair { readonly tag: 'Pair'; readonly fst: Surface; readonly snd: Surface }
export const Pair = (fst: Surface, snd: Surface): Pair => ({ tag: 'Pair', fst, snd });
export interface IndSigma { readonly tag: 'IndSigma'; readonly usage: Usage; readonly motive: Surface | null; readonly scrut: Surface, readonly cas: Surface }
export const IndSigma = (usage: Usage, motive: Surface | null, scrut: Surface, cas: Surface): IndSigma => ({ tag: 'IndSigma', usage, motive, scrut, cas });

export const flattenPi = (t: Surface): [[Usage, Mode, Name, Surface][], Surface] => {
  const params: [Usage, Mode, Name, Surface][] = [];
  let c = t;  
  while (c.tag === 'Pi') {
    params.push([c.usage, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenAbs = (t: Surface): [[Usage, Mode, Name, Surface | null][], Surface] => {
  const params: [Usage, Mode, Name, Surface | null][] = [];
  let c = t;  
  while (c.tag === 'Abs') {
    params.push([c.usage, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenApp = (t: Surface): [Surface, [Mode, Surface][]] => {
  const args: [Mode, Surface][] = [];
  let c = t;  
  while (c.tag === 'App') {
    args.push([c.mode, c.arg]);
    c = c.fn;
  }
  return [c, args.reverse()];
};
export const flattenSigma = (t: Surface): [[Usage, Name, Surface][], Surface] => {
  const params: [Usage, Name, Surface][] = [];
  let c = t;  
  while (c.tag === 'Sigma') {
    params.push([c.usage, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenPair = (t: Surface): Surface[] => {
  const r: Surface[] = [];
  while (t.tag === 'Pair') {
    r.push(t.fst);
    t = t.snd;
  }
  r.push(t);
  return r;
};

const showP = (b: boolean, t: Surface) => b ? `(${show(t)})` : show(t);
const isSimple = (t: Surface) => t.tag === 'Type' || t.tag === 'Var';
const showS = (t: Surface) => showP(!isSimple(t), t);
export const show = (t: Surface): string => {
  if (t.tag === 'Type') return 'Type';
  if (t.tag === 'Var') return `${t.name}`;
  if (t.tag === 'Pi') {
    const [params, ret] = flattenPi(t);
    return `${params.map(([u, m, x, t]) => u === many && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${u === many ? '' : `${u} `}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' -> ')} -> ${show(ret)}`;
  }
  if (t.tag === 'Abs') {
    const [params, body] = flattenAbs(t);
    return `\\${params.map(([u, m, x, t]) => u === many && m.tag === 'Expl' && !t ? x : `${m.tag === 'Expl' ? '(' : '{'}${u === many ? '' : `${u} `}${x}${t ? ` : ${show(t)}` : ''}${m.tag === 'Expl' ? ')' : '}'}`).join(' ')}. ${show(body)}`;
  }
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${show(a)}}`).join(' ')}`;
  }
  if (t.tag === 'Let')
    return `let ${t.usage === many ? '' : `${t.usage} `}${t.name}${t.type ? ` : ${showP(t.type.tag === 'Let', t.type)}` : ''} = ${showP(t.val.tag === 'Let', t.val)}; ${show(t.body)}`;
  if (t.tag === 'Sigma') {
    const [params, ret] = flattenSigma(t);
    return `${params.map(([u, x, t]) => u === many && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `(${u === many ? '' : `${u} `}${x} : ${show(t)})`).join(' ** ')} ** ${show(ret)}`;
  }
  if (t.tag === 'Pair') {
    const ps = flattenPair(t);
    return `(${ps.map(show).join(', ')})`;
  }
  if (t.tag === 'IndSigma')
    return `indSigma ${t.usage === many ? '' : `${t.usage} `}${t.motive ? `{${show(t.motive)}} ` : ''}${showS(t.scrut)} ${showS(t.cas)}`;
  return t;
};

export const fromCore = (t: Core, ns: List<Name> = nil): Surface => {
  if (t.tag === 'Type') return Type;
  if (t.tag === 'Var') return Var(ns.index(t.index) || impossible(`var out of scope in fromCore: ${t.index}`));
  if (t.tag === 'Global') return Var(t.name);
  if (t.tag === 'App') return App(fromCore(t.fn, ns), t.mode, fromCore(t.arg, ns));
  if (t.tag === 'Pi') {
    const x = chooseName(t.name, ns);
    return Pi(t.usage, t.mode, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Abs') {
    const x = chooseName(t.name, ns);
    return Abs(t.usage, t.mode, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Let') {
    const x = chooseName(t.name, ns);
    return Let(t.usage, x, fromCore(t.type, ns), fromCore(t.val, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Sigma') {
    const x = chooseName(t.name, ns);
    return Sigma(t.usage, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Pair') return Pair(fromCore(t.fst, ns), fromCore(t.snd, ns));
  if (t.tag === 'IndSigma') return IndSigma(t.usage, fromCore(t.motive, ns), fromCore(t.scrut, ns), fromCore(t.cas, ns));
  return t;
};

export const showCore = (t: Core, ns: List<Name> = nil): string => show(fromCore(t, ns));
export const showVal = (v: Val, k: Lvl = 0, ns: List<Name> = nil): string => show(fromCore(quote(v, k), ns));

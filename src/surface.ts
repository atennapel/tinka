import { MetaVar } from './metas';
import { Erasure, Mode } from './mode';
import { chooseName, Ix, Lvl, Name } from './names';
import { Core } from './core';
import { cons, List, nil } from './utils/List';
import { impossible } from './utils/utils';
import { quote, Val } from './values';
import { config } from './config';

export type Surface =
  Var | Let | Ann |
  Pi | Abs | App |
  Sigma | Pair | Proj |
  Import |
  Meta | Hole | Rigid;

export interface Var { readonly tag: 'Var'; readonly name: Name }
export const Var = (name: Name): Var => ({ tag: 'Var', name });
export interface Let { readonly tag: 'Let'; readonly erased: Erasure; readonly name: Name; readonly type: Surface | null; readonly val: Surface; readonly body: Surface }
export const Let = (erased: Erasure, name: Name, type: Surface | null, val: Surface, body: Surface): Let => ({ tag: 'Let', erased, name, type, val, body });
export interface Ann { readonly tag: 'Ann'; readonly term: Surface; readonly type: Surface }
export const Ann = (term: Surface, type: Surface): Ann => ({ tag: 'Ann', term, type });

export interface Pi { readonly tag: 'Pi'; readonly erased: Erasure; readonly mode: Mode; readonly name: Name; readonly type: Surface; readonly body: Surface; }
export const Pi = (erased: Erasure, mode: Mode, name: Name, type: Surface, body: Surface): Pi => ({ tag: 'Pi', erased, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly erased: Erasure; readonly mode: Mode; readonly name: Name; readonly type: Surface | null; readonly body: Surface }
export const Abs = (erased: Erasure, mode: Mode, name: Name, type: Surface | null, body: Surface): Abs => ({ tag: 'Abs', erased, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Surface; readonly mode: Mode; readonly arg: Surface }
export const App = (fn: Surface, mode: Mode, arg: Surface): App => ({ tag: 'App', fn, mode, arg });

export interface Sigma { readonly tag: 'Sigma'; readonly erased: Erasure; readonly name: Name; readonly type: Surface; readonly body: Surface }
export const Sigma = (erased: Erasure, name: Name, type: Surface, body: Surface): Sigma => ({ tag: 'Sigma', erased, name, type, body });
export interface Pair { readonly tag: 'Pair'; readonly fst: Surface; readonly snd: Surface }
export const Pair = (fst: Surface, snd: Surface): Pair => ({ tag: 'Pair', fst, snd });
export interface Proj { readonly tag: 'Proj'; readonly term: Surface; readonly proj: ProjType }
export const Proj = (term: Surface, proj: ProjType): Proj => ({ tag: 'Proj', term, proj });

export interface Import { readonly tag: 'Import'; readonly term: Surface; readonly imports: string[] | null; readonly body: Surface }
export const Import = (term: Surface, imports: string[] | null, body: Surface): Import => ({ tag: 'Import', term, imports, body });

export interface Meta { readonly tag: 'Meta'; readonly id: MetaVar }
export const Meta = (id: MetaVar): Meta => ({ tag: 'Meta', id });
export interface Hole { readonly tag: 'Hole'; readonly name: Name | null }
export const Hole = (name: Name | null): Hole => ({ tag: 'Hole', name });
export interface Rigid { readonly tag: 'Rigid'; readonly term: Surface }
export const Rigid = (term: Surface): Rigid => ({ tag: 'Rigid', term });

export type ProjType = PProj | PName | PIndex;

export interface PProj { readonly tag: 'PProj'; readonly proj: 'fst' | 'snd' }
export const PProj = (proj: 'fst' | 'snd'): PProj => ({ tag: 'PProj', proj });
export const PFst = PProj('fst');
export const PSnd = PProj('snd');
export interface PName { readonly tag: 'PName'; readonly name: Name }
export const PName = (name: Name): PName => ({ tag: 'PName', name });
export interface PIndex { readonly tag: 'PIndex'; readonly index: Ix }
export const PIndex = (index: Ix): PIndex => ({ tag: 'PIndex', index });

export const Type = Var('*');

export const flattenPi = (t: Surface): [[Erasure, Mode, Name, Surface][], Surface] => {
  const params: [Erasure, Mode, Name, Surface][] = [];
  let c = t;  
  while (c.tag === 'Pi') {
    params.push([c.erased, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenSigma = (t: Surface): [[Erasure, Name, Surface][], Surface] => {
  const params: [Erasure, Name, Surface][] = [];
  let c = t;  
  while (c.tag === 'Sigma') {
    params.push([c.erased, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenAbs = (t: Surface): [[Erasure, Mode, Name, Surface | null][], Surface] => {
  const params: [Erasure, Mode, Name, Surface | null][] = [];
  let c = t;  
  while (c.tag === 'Abs') {
    params.push([c.erased, c.mode, c.name, c.type]);
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
export const flattenPair = (t: Surface): [Surface[], Surface] => {
  const ps: Surface[] = [];
  let c = t;
  while (c.tag === 'Pair') {
    ps.push(c.fst);
    c = c.snd;
  }
  return [ps, c];
};
export const flattenProj = (t: Surface): [Surface, ProjType[]] => {
  const r: ProjType[] = [];
  while (t.tag === 'Proj') {
    r.push(t.proj);
    t = t.term;
  }
  return [t, r.reverse()];
};

const showP = (b: boolean, t: Surface) => b ? `(${show(t)})` : show(t);
const appIsSimple = (t: Surface): boolean => {
  if (!config.hideImplicits) return false;
  if (t.tag !== 'App') return false;
  const [fn, args] = flattenApp(t);
  return !args.some(([m]) => m.tag === 'Expl') && isSimple(fn);
};
const isSimple = (t: Surface) => t.tag === 'Var' || t.tag === 'Hole' || t.tag === 'Meta' || t.tag === 'Pair' || t.tag === 'Proj' || appIsSimple(t);
const showS = (t: Surface) => showP(!isSimple(t), t);
const showProjType = (p: ProjType): string => {
  if (p.tag === 'PProj') return p.proj === 'fst' ? '_1' : '_2';
  if (p.tag === 'PName') return `${p.name}`;
  if (p.tag === 'PIndex') return `${p.index}`;
  return p;
};
export const show = (t: Surface): string => {
  if (t.tag === 'Var') return t.name === '*' && config.unicode ? '★' : `${t.name}`;
  if (t.tag === 'Hole') return `_${t.name === null ? '' : t.name}`;
  if (t.tag === 'Meta') return `?${t.id}`;
  if (t.tag === 'Pi') {
    const [params, ret] = flattenPi(t);
    const arr = config.unicode ? '→' : '->';
    return `${params.map(([e, m, x, t]) => !e && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${e ? '-' : ''}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(` ${arr} `)} ${arr} ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
  }
  if (t.tag === 'Abs') {
    const [params1, body] = flattenAbs(t);
    const params = config.hideImplicits ? params1.filter(([_, m]) => m.tag === 'Expl') : params1;
    return `${config.unicode ? 'λ' : '\\'}${params.map(([e, m, x, t]) => `${m.tag === 'Impl' ? '{' : t ? '(' : ''}${e ? '-' : ''}${x}${t ? ` : ${show(t)}` : ''}${m.tag === 'Impl' ? '}' : t ? ')' : ''}`).join(' ')}. ${show(body)}`;
  }
  if (t.tag === 'App') {
    const [fn, args1] = flattenApp(t);
    const args = config.hideImplicits ? args1.filter(([m]) => m.tag === 'Expl') : args1;
    return `${showS(fn)}${args.length > 0 ? ' ' : ''}${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${show(a)}}`).join(' ')}`;
  }
  if (t.tag === 'Sigma') {
    const [params, ret] = flattenSigma(t);
    const prod = config.unicode ? '×' : '**';
    return `${params.map(([e, x, t]) => !e && x === '_' ? showP(t.tag === 'Sigma' || t.tag === 'Pi' || t.tag === 'Let', t) : `(${e ? '-' : ''}${x} : ${show(t)})`).join(` ${prod} `)} ${prod} ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
  }
  if (t.tag === 'Pair') {
    const [ps, ret] = flattenPair(t);
    if (ret.tag === 'Var' && ret.name === '[]')
      return `[${ps.map(show).join(', ')}]`;
    return `(${ps.map(show).join(', ')}, ${show(ret)})`;
  }
  if (t.tag === 'Let')
    return `let ${t.erased ? '-' : ''}${t.name}${t.type ? ` : ${showP(t.type.tag === 'Let', t.type)}` : ''} = ${showP(t.val.tag === 'Let', t.val)}; ${show(t.body)}`;
  if (t.tag === 'Proj') {
    const [hd, ps] = flattenProj(t);
    return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
  }
  if (t.tag === 'Ann') return `${show(t.term)} : ${show(t.type)}`;
  if (t.tag === 'Import')
    return `import ${showS(t.term)}${t.imports ? ` (${t.imports.join(', ')})` : ''}; ${show(t.body)}`;
  if (t.tag === 'Rigid') return `@${showS(t.term)}`;
  return t;
};

export const fromCore = (t: Core, ns: List<Name> = nil): Surface => {
  if (t.tag === 'Var') return Var(ns.index(t.index) || impossible(`var out of scope in fromCore: ${t.index}`));
  if (t.tag === 'Global') return Var(t.name);
  if (t.tag === 'Prim') return Var(t.name);
  if (t.tag === 'App') return App(fromCore(t.fn, ns), t.mode, fromCore(t.arg, ns));
  if (t.tag === 'Pi') {
    const x = chooseName(t.name, ns);
    return Pi(t.erased, t.mode, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Abs') {
    const x = chooseName(t.name, ns);
    return Abs(t.erased, t.mode, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Let') {
    // de-elaborate annotations
    if (t.body.tag === 'Var' && t.body.index === 0)
      return Ann(fromCore(t.val, ns), fromCore(t.type, ns));
    const x = chooseName(t.name, ns);
    return Let(t.erased, x, fromCore(t.type, ns), fromCore(t.val, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Sigma') {
    const x = chooseName(t.name, ns);
    return Sigma(t.erased, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Pair') return Pair(fromCore(t.fst, ns), fromCore(t.snd, ns));
  if (t.tag === 'Proj') return Proj(fromCore(t.term, ns), t.proj.tag === 'PProj' ? t.proj : t.proj.name ? PName(t.proj.name) : PIndex(t.proj.index));
  if (t.tag === 'Meta' || t.tag === 'InsertedMeta') return Meta(t.id);
  return t;
};

export const showCore = (t: Core, ns: List<Name> = nil): string => show(fromCore(t, ns));
export const showVal = (v: Val, k: Lvl = 0, full: boolean = false, ns: List<Name> = nil): string => show(fromCore(quote(v, k, full), ns));

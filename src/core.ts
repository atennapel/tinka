import { MetaVar } from './metas';
import { Erasure, Mode } from './mode';
import { Ix, Name } from './names';
import { PrimName } from './prims';
import { List } from './utils/List';

export type Core =
  Var | Global | Prim | Let |
  Pi | Abs | App |
  Sigma | Pair | Proj |
  Meta | InsertedMeta;

export interface Var { readonly tag: 'Var'; readonly index: Ix }
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export interface Global { readonly tag: 'Global'; readonly name: Name}
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export interface Prim { readonly tag: 'Prim'; readonly name: PrimName }
export const Prim = (name: PrimName): Prim => ({ tag: 'Prim', name });
export interface Let { readonly tag: 'Let'; readonly erased: Erasure; readonly name: Name; readonly type: Core; readonly val: Core; readonly body: Core }
export const Let = (erased: Erasure, name: Name, type: Core, val: Core, body: Core): Let => ({ tag: 'Let', erased, name, type, val, body });

export interface Pi { readonly tag: 'Pi'; readonly erased: Erasure; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core; }
export const Pi = (erased: Erasure, mode: Mode, name: Name, type: Core, body: Core): Pi => ({ tag: 'Pi', erased, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly erased: Erasure; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Abs = (erased: Erasure, mode: Mode, name: Name, type: Core, body: Core): Abs => ({ tag: 'Abs', erased, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Core; readonly mode: Mode; readonly arg: Core }
export const App = (fn: Core, mode: Mode, arg: Core): App => ({ tag: 'App', fn, mode, arg });

export interface Sigma { readonly tag: 'Sigma'; readonly erased: Erasure; readonly name: Name; readonly type: Core; readonly body: Core }
export const Sigma = (erased: Erasure, name: Name, type: Core, body: Core): Sigma => ({ tag: 'Sigma', erased, name, type, body });
export interface Pair { readonly tag: 'Pair'; readonly fst: Core; readonly snd: Core; readonly type: Core }
export const Pair = (fst: Core, snd: Core, type: Core): Pair => ({ tag: 'Pair', fst, snd, type });
export interface Proj { readonly tag: 'Proj'; readonly term: Core; readonly proj: ProjType }
export const Proj = (term: Core, proj: ProjType): Proj => ({ tag: 'Proj', term, proj });

export interface Meta { readonly tag: 'Meta'; readonly id: MetaVar }
export const Meta = (id: MetaVar): Meta => ({ tag: 'Meta', id });
export interface InsertedMeta { readonly tag: 'InsertedMeta'; readonly id: MetaVar; readonly spine: List<[Mode, boolean]> }
export const InsertedMeta = (id: MetaVar, spine: List<[Mode, boolean]>): InsertedMeta => ({ tag: 'InsertedMeta', id, spine });

export type ProjType = PProj | PIndex;

export interface PProj { readonly tag: 'PProj'; readonly proj: 'fst' | 'snd' }
export const PProj = (proj: 'fst' | 'snd'): PProj => ({ tag: 'PProj', proj });
export const PFst = PProj('fst');
export const PSnd = PProj('snd');
export interface PIndex { readonly tag: 'PIndex'; readonly name: Name | null; readonly index: Ix }
export const PIndex = (name: Name | null, index: Ix): PIndex => ({ tag: 'PIndex', name, index });

export const Type = Prim('*');
export const UnitType = Prim('()');
export const Unit = Prim('Unit');

export const flattenPi = (t: Core): [[Erasure, Mode, Name, Core][], Core] => {
  const params: [Erasure, Mode, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Pi') {
    params.push([c.erased, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenSigma = (t: Core): [[Erasure, Name, Core][], Core] => {
  const params: [Erasure, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Sigma') {
    params.push([c.erased, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenAbs = (t: Core): [[Erasure, Mode, Name, Core][], Core] => {
  const params: [Erasure, Mode, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Abs') {
    params.push([c.erased, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenApp = (t: Core): [Core, [Mode, Core][]] => {
  const args: [Mode, Core][] = [];
  let c = t;  
  while (c.tag === 'App') {
    args.push([c.mode, c.arg]);
    c = c.fn;
  }
  return [c, args.reverse()];
};
export const flattenPair = (t: Core): [Core[], Core] => {
  const ps: Core[] = [];
  let c = t;
  while (c.tag === 'Pair') {
    ps.push(c.fst);
    c = c.snd;
  }
  return [ps, c];
};
export const flattenProj = (t: Core): [Core, ProjType[]] => {
  const r: ProjType[] = [];
  while (t.tag === 'Proj') {
    r.push(t.proj);
    t = t.term;
  }
  return [t, r.reverse()];
};

const showP = (b: boolean, t: Core) => b ? `(${show(t)})` : show(t);
const isSimple = (t: Core) => t.tag === 'Var' || t.tag === 'Global' || t.tag === 'Prim' || t.tag === 'Meta' || t.tag === 'InsertedMeta' || t.tag === 'Pair' || t.tag === 'Proj';
const showS = (t: Core) => showP(!isSimple(t), t);
const showProjType = (p: ProjType): string => {
  if (p.tag === 'PProj') return p.proj === 'fst' ? '_1' : '_2';
  if (p.tag === 'PIndex') return p.name ? `${p.name}` : `${p.index}`;
  return p;
};
export const show = (t: Core): string => {
  if (t.tag === 'Var') return `'${t.index}`;
  if (t.tag === 'Global') return `${t.name}`;
  if (t.tag === 'Prim') {
    if (t.name === '*') return t.name;
    if (t.name === '()') return t.name;
    return `%${t.name}`;
  }
  if (t.tag === 'Meta') return `?${t.id}`;
  if (t.tag === 'InsertedMeta') return `?*${t.id}${t.spine.reverse().toString(([m, b]) => `${m.tag === 'Expl' ? '' : '{'}${b ? 'b' : 'd'}${m.tag === 'Expl' ? '' : '}'}`)}`;
  if (t.tag === 'Pi') {
    const [params, ret] = flattenPi(t);
    return `${params.map(([e, m, x, t]) => !e && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${e ? '-' : ''}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' -> ')} -> ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
  }
  if (t.tag === 'Abs') {
    const [params, body] = flattenAbs(t);
    return `\\${params.map(([e, m, x, t]) => `${m.tag === 'Impl' ? '{' : '('}${e ? '-' : ''}${x} : ${show(t)}${m.tag === 'Impl' ? '}' : ')'}`).join(' ')}. ${show(body)}`;
  }
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${show(a)}}`).join(' ')}`;
  }
  if (t.tag === 'Sigma') {
    const [params, ret] = flattenSigma(t);
    return `${params.map(([e, x, t]) => !e && x === '_' ? showP(t.tag === 'Sigma' || t.tag === 'Pi' || t.tag === 'Let', t) : `(${e ? '-' : ''}${x} : ${show(t)})`).join(' ** ')} ** ${showP(ret.tag === 'Sigma' || ret.tag === 'Pi' || ret.tag === 'Let', ret)}`;
  }
  if (t.tag === 'Pair') {
    const [ps, ret] = flattenPair(t);
    return `(${ps.map(show).join(', ')}, ${show(ret)}) : ${show(t.type)}`;
  }
  if (t.tag === 'Let')
    return `let ${t.erased ? '-' : ''}${t.name} : ${showP(t.type.tag === 'Let', t.type)} = ${showP(t.val.tag === 'Let', t.val)}; ${show(t.body)}`;
  if (t.tag === 'Proj') {
    const [hd, ps] = flattenProj(t);
    return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
  }
  return t;
};

export const shift = (d: Ix, c: Ix, t: Core): Core => {
  if (t.tag === 'Var') return t.index < c ? t : Var(t.index + d);
  if (t.tag === 'App') return App(shift(d, c, t.fn), t.mode, shift(d, c, t.arg));
  if (t.tag === 'Abs') return Abs(t.erased, t.mode, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Pair') return Pair(shift(d, c, t.fst), shift(d, c, t.snd), shift(d, c, t.type));
  if (t.tag === 'Proj') return Proj(shift(d, c, t.term), t.proj);
  if (t.tag === 'Let') return Let(t.erased, t.name, shift(d, c, t.type), shift(d, c, t.val), shift(d, c + 1, t.body));
  if (t.tag === 'Pi') return Pi(t.erased, t.mode, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Sigma') return Sigma(t.erased, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  return t;
};

export const substVar = (j: Ix, s: Core, t: Core): Core => {
  if (t.tag === 'Var') return t.index === j ? s : t;
  if (t.tag === 'App') return App(substVar(j, s, t.fn), t.mode, substVar(j, s, t.arg));
  if (t.tag === 'Abs') return Abs(t.erased, t.mode, t.name, substVar(j, s, t.type), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'Pair') return Pair(substVar(j, s, t.fst), substVar(j, s, t.snd), substVar(j, s, t.type));
  if (t.tag === 'Proj') return Proj(substVar(j, s, t.term), t.proj);
  if (t.tag === 'Let') return Let(t.erased, t.name, substVar(j, s, t.type), substVar(j, s, t.val), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'Pi') return Pi(t.erased, t.mode, t.name, substVar(j, s, t.type), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'Sigma') return Sigma(t.erased, t.name, substVar(j, s, t.type), substVar(j + 1, shift(1, 0, s), t.body));
  return t;
};

export const subst = (t: Core, u: Core): Core => shift(-1, 0, substVar(0, shift(1, 0, u), t));

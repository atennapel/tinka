import { Core } from './core';
import { Mode } from './mode';
import { chooseName, Ix, Lvl, Name } from './names';
import { PrimElimName, PrimElimNames, PrimNames } from './prims';
import { many, one, Usage } from './usage';
import { cons, List, nil } from './utils/List';
import { impossible, pushUniq, remove, removeAll } from './utils/utils';
import { quote, Val } from './values';

export type Surface =
  Var | Let | Hole | Ann |
  Pi | Abs | App |
  Sigma | Pair | Proj |
  Signature | Module | Import |
  PropEq | Refl |
  PrimElim;

export interface Var { readonly tag: 'Var'; readonly name: Name }
export const Var = (name: Name): Var => ({ tag: 'Var', name });
export interface Let { readonly tag: 'Let'; readonly usage: Usage; readonly name: Name; readonly type: Surface | null; readonly val: Surface; readonly body: Surface }
export const Let = (usage: Usage, name: Name, type: Surface | null, val: Surface, body: Surface): Let => ({ tag: 'Let', usage, name, type, val, body });
export interface Ann { readonly tag: 'Ann'; readonly term: Surface; readonly type: Surface }
export const Ann = (term: Surface, type: Surface): Ann => ({ tag: 'Ann', term, type });
export interface Pi { readonly tag: 'Pi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Surface; readonly body: Surface }
export const Pi = (usage: Usage, mode: Mode, name: Name, type: Surface, body: Surface): Pi =>
  ({ tag: 'Pi', usage, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Surface | null; readonly body: Surface }
export const Abs = (usage: Usage, mode: Mode, name: Name, type: Surface | null, body: Surface): Abs =>
  ({ tag: 'Abs', usage, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Surface; readonly mode: Mode; readonly arg: Surface }
export const App = (fn: Surface, mode: Mode, arg: Surface): App => ({ tag: 'App', fn, mode, arg });
export interface Sigma { readonly tag: 'Sigma'; readonly usage: Usage; readonly exclusive: boolean; readonly name: Name; readonly type: Surface; readonly body: Surface }
export const Sigma = (usage: Usage, exclusive: boolean, name: Name, type: Surface, body: Surface): Sigma => ({ tag: 'Sigma', usage, exclusive, name, type, body });
export interface Pair { readonly tag: 'Pair'; readonly fst: Surface; readonly snd: Surface }
export const Pair = (fst: Surface, snd: Surface): Pair => ({ tag: 'Pair', fst, snd });
export interface Proj { readonly tag: 'Proj'; readonly term: Surface; readonly proj: ProjType }
export const Proj = (term: Surface, proj: ProjType): Proj => ({ tag: 'Proj', term, proj });
export interface Import { readonly tag: 'Import'; readonly term: Surface; readonly imports: string[] | null; readonly body: Surface }
export const Import = (term: Surface, imports: string[] | null, body: Surface): Import => ({ tag: 'Import', term, imports, body });
export interface SigEntry { readonly usage: Usage; readonly name: Name; readonly type: Surface | null }
export const SigEntry = (usage: Usage, name: Name, type: Surface | null): SigEntry => ({ usage, name, type });
export interface Signature { readonly tag: 'Signature'; readonly defs: SigEntry[] }
export const Signature = (defs: SigEntry[]): Signature => ({ tag: 'Signature', defs });
export interface ModEntry { readonly priv: boolean; readonly usage: Usage; readonly name: Name; readonly type: Surface | null; readonly val: Surface }
export const ModEntry = (priv: boolean, usage: Usage, name: Name, type: Surface | null, val: Surface): ModEntry => ({ priv, usage, name, type, val });
export interface Module { readonly tag: 'Module'; readonly defs: ModEntry[] }
export const Module = (defs: ModEntry[]): Module => ({ tag: 'Module', defs });
export interface PropEq { readonly tag: 'PropEq'; readonly type: Surface | null; readonly left: Surface; readonly right: Surface }
export const PropEq = (type: Surface | null, left: Surface, right: Surface): PropEq => ({ tag: 'PropEq', type, left, right });
export interface Refl { readonly tag: 'Refl'; readonly type: Surface | null; readonly val: Surface | null };
export const Refl = (type: Surface | null, val: Surface | null): Refl => ({ tag: 'Refl', type, val });
export interface Hole { readonly tag: 'Hole'; readonly name: Name | null }
export const Hole = (name: Name | null): Hole => ({ tag: 'Hole', name });
export interface PrimElim { readonly tag: 'PrimElim'; readonly name: PrimElimName; readonly usage: Usage; readonly motive: Surface; readonly scrut: Surface; readonly cases: Surface[] }
export const PrimElim = (name: PrimElimName, usage: Usage, motive: Surface, scrut: Surface, cases: Surface[]): PrimElim => ({ tag: 'PrimElim', name, usage, motive, scrut, cases });

export const UnitType = Var('()');
export const Unit = Var('*');

export type ProjType = PProj | PName | PIndex;

export interface PProj { readonly tag: 'PProj'; readonly proj: 'fst' | 'snd' }
export const PProj = (proj: 'fst' | 'snd'): PProj => ({ tag: 'PProj', proj });
export const PFst = PProj('fst');
export const PSnd = PProj('snd');
export interface PName { readonly tag: 'PName'; readonly name: Name }
export const PName = (name: Name): PName => ({ tag: 'PName', name });
export interface PIndex { readonly tag: 'PIndex'; readonly index: Ix }
export const PIndex = (index: Ix): PIndex => ({ tag: 'PIndex', index });

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
export const flattenSigma = (t: Surface): [[Usage, boolean, Name, Surface][], Surface] => {
  const params: [Usage, boolean, Name, Surface][] = [];
  let c = t;  
  while (c.tag === 'Sigma') {
    params.push([c.usage, c.exclusive, c.name, c.type]);
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
export const flattenProj = (t: Surface): [Surface, ProjType[]] => {
  const r: ProjType[] = [];
  while (t.tag === 'Proj') {
    r.push(t.proj);
    t = t.term;
  }
  return [t, r.reverse()];
};

const showP = (b: boolean, t: Surface) => b ? `(${show(t)})` : show(t);
const isSimple = (t: Surface) => t.tag === 'Var' || t.tag === 'Proj' || t.tag === 'Hole';
const showS = (t: Surface) => showP(!isSimple(t), t);
const showProjType = (p: ProjType): string => {
  if (p.tag === 'PProj') return p.proj === 'fst' ? '_1' : '_2';
  if (p.tag === 'PName') return `${p.name}`;
  if (p.tag === 'PIndex') return `${p.index}`;
  return p;
};
export const show = (t: Surface): string => {
  if (t.tag === 'Var') return `${t.name}`;
  if (t.tag === 'Hole') return `_${t.name || ''}`;
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
  if (t.tag === 'Import')
    return `import ${showS(t.term)}${t.imports ? ` (${t.imports.join(', ')})` : ''}; ${show(t.body)}`
  if (t.tag === 'Sigma') {
    const [params, ret] = flattenSigma(t);
    const ps = params.map(([u, e, x, ty]) => {
      const param = u === many && x === '_' ? showP(ty.tag === 'Pi' || ty.tag === 'Sigma' || ty.tag === 'Let', ty) : `(${u === many ? '' : `${u} `}${x} : ${show(ty)})`;
      return `${param} ${e ? '||' : '**'} `;
    }).join('');
    return `${ps}${show(ret)}`;
  }
  if (t.tag === 'Pair') {
    const ps = flattenPair(t);
    return `(${ps.map(show).join(', ')})`;
  }
  if (t.tag === 'Proj') {
    const [hd, ps] = flattenProj(t);
    return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
  }
  if (t.tag === 'Signature')
    return `sig { ${t.defs.map(({usage, name, type}) => `def ${usage === many ? '' : `${usage} `}${name}${type ? ` : ${show(type)}` : ''}`).join(' ')} }`;
  if (t.tag === 'Module')
    return `mod { ${t.defs.map(({priv, usage, name, type, val}) =>
      `${priv ? 'private ' : ''}def ${usage === many ? '' : `${usage} `}${name}${type ? ` : ${show(type)}` : ''} = ${show(val)}`).join(' ')} }`;
  if (t.tag === 'PropEq')
    return `${t.type ? `{${show(t.type)}} ` : ''}${show(t.left)} = ${show(t.right)}`;
  if (t.tag === 'Refl') return `Refl${t.type ? ` {${show(t.type)}}` : ''}${t.val ? ` {${show(t.val)}}` : ''}`;
  if (t.tag === 'PrimElim')
    return `${t.name} ${t.usage === many ? '' : `${t.usage} `}${showS(t.motive)} ${showS(t.scrut)}${t.cases.map(c => ` ${showS(c)}`).join('')}`;
  if (t.tag === 'Ann')
    return `${show(t.term)} : ${show(t.type)}`;
  return t;
};

export const fromCore = (t: Core, ns: List<Name> = nil): Surface => {
  if (t.tag === 'Var') return Var(ns.index(t.index) || impossible(`var out of scope in fromCore: ${t.index}`));
  if (t.tag === 'Global') return Var(t.name);
  if (t.tag === 'Prim') return Var(t.name);
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
    // de-elaborate annotations
    if (t.usage === one && t.body.tag === 'Var' && t.body.index === 0)
      return Ann(fromCore(t.val, ns), fromCore(t.type, ns));
    const x = chooseName(t.name, ns);
    return Let(t.usage, x, fromCore(t.type, ns), fromCore(t.val, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Sigma') {
    const x = chooseName(t.name, ns);
    return Sigma(t.usage, t.exclusive, x, fromCore(t.type, ns), fromCore(t.body, cons(x, ns)));
  }
  if (t.tag === 'Pair') return Pair(fromCore(t.fst, ns), fromCore(t.snd, ns));
  if (t.tag === 'Proj') return Proj(fromCore(t.term, ns), t.proj.tag === 'PProj' ? t.proj : t.proj.name ? PName(t.proj.name) : PIndex(t.proj.index));
  if (t.tag === 'PropEq') return PropEq(fromCore(t.type, ns), fromCore(t.left, ns), fromCore(t.right, ns));
  if (t.tag === 'Refl') return Refl(fromCore(t.type, ns), fromCore(t.val, ns));
  if (t.tag === 'PrimElim') return PrimElim(t.name, t.usage, fromCore(t.motive, ns), fromCore(t.scrut, ns), t.cases.map(x => fromCore(x, ns)));
  return t;
};

export const showCore = (t: Core, ns: List<Name> = nil): string => show(fromCore(t, ns));
export const showVal = (v: Val, k: Lvl = 0, ns: List<Name> = nil): string => show(fromCore(quote(v, k), ns));

export const freeVarsAll = (t: Surface, a: Name[] = []): Name[] => {
  if (t.tag === 'Var') return pushUniq(a, t.name);
  if (t.tag === 'Hole') return a;
  if (t.tag === 'Pi') {
    freeVarsAll(t.body, a);
    remove(a, t.name);
    return freeVarsAll(t.type, a);
  }
  if (t.tag === 'Abs') {
    freeVarsAll(t.body, a);
    remove(a, t.name);
    return t.type ? freeVarsAll(t.type, a) : a;
  }
  if (t.tag === 'App') {
    freeVarsAll(t.fn, a);
    return freeVarsAll(t.arg, a);
  }
  if (t.tag === 'Let') {
    freeVarsAll(t.body, a);
    remove(a, t.name);
    freeVarsAll(t.val, a);
    return t.type ? freeVarsAll(t.type, a) : a;
  }
  if (t.tag === 'Import') return freeVarsAll(t.term, a);
  if (t.tag === 'Sigma') {
    freeVarsAll(t.body, a);
    remove(a, t.name);
    return freeVarsAll(t.type, a);
  }
  if (t.tag === 'Pair') {
    freeVarsAll(t.fst, a);
    return freeVarsAll(t.snd, a);
  }
  if (t.tag === 'Proj') return freeVarsAll(t.term, a);
  if (t.tag === 'Signature') {
    t.defs.forEach(d => { if (d.type) freeVarsAll(d.type, a) });
    return a;
  }
  if (t.tag === 'Module') {
    t.defs.forEach(d => {
      freeVarsAll(d.val, a);
      if (d.type) freeVarsAll(d.type, a);
    });
    return a;
  }
  if (t.tag === 'PropEq') {
    freeVarsAll(t.left, a);
    freeVarsAll(t.right, a);
    return t.type ? freeVarsAll(t.type, a) : a;
  }
  if (t.tag === 'Refl') {
    if (t.val) freeVarsAll(t.val, a);
    return t.type ? freeVarsAll(t.type, a) : a;
  }
  if (t.tag === 'PrimElim') {
    freeVarsAll(t.motive, a);
    freeVarsAll(t.scrut, a);
    t.cases.forEach(x => freeVarsAll(x, a));
    return a;
  }
  if (t.tag === 'Ann') {
    freeVarsAll(t.term, a);
    return freeVarsAll(t.type, a);
  }
  return t;
};

export const freeVars = (t: Surface): Name[] => {
  const vs = freeVarsAll(t);
  remove(vs, '_');
  removeAll(vs, PrimNames);
  removeAll(vs, PrimElimNames);
  return vs;
};

import { Mode } from './mode';
import { Ix, Name } from './names';
import { many, Usage } from './usage';

export type Core =
  Var | Global | Let |
  Type |
  Pi | Abs | App |
  Sigma | Pair | ElimSigma | Proj |
  PropEq | Refl;

export interface Var { readonly tag: 'Var'; readonly index: Ix }
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export interface Global { readonly tag: 'Global'; readonly name: Name }
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export interface Let { readonly tag: 'Let'; readonly usage: Usage; readonly name: Name; readonly type: Core; readonly val: Core; readonly body: Core }
export const Let = (usage: Usage, name: Name, type: Core, val: Core, body: Core): Let => ({ tag: 'Let', usage, name, type, val, body });
export interface Type { readonly tag: 'Type' }
export const Type: Type = { tag: 'Type' };
export interface Pi { readonly tag: 'Pi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Pi = (usage: Usage, mode: Mode, name: Name, type: Core, body: Core): Pi =>
  ({ tag: 'Pi', usage, mode, name, type, body });
export interface Abs { readonly tag: 'Abs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Core; readonly body: Core }
export const Abs = (usage: Usage, mode: Mode, name: Name, type: Core, body: Core): Abs =>
  ({ tag: 'Abs', usage, mode, name, type, body });
export interface App { readonly tag: 'App'; readonly fn: Core; readonly mode: Mode; readonly arg: Core }
export const App = (fn: Core, mode: Mode, arg: Core): App => ({ tag: 'App', fn, mode, arg });
export interface Sigma { readonly tag: 'Sigma'; readonly usage: Usage; readonly name: Name; readonly type: Core; readonly body: Core }
export const Sigma = (usage: Usage, name: Name, type: Core, body: Core): Sigma => ({ tag: 'Sigma', usage, name, type, body });
export interface Pair { readonly tag: 'Pair'; readonly fst: Core; readonly snd: Core; readonly type: Core }
export const Pair = (fst: Core, snd: Core, type: Core): Pair => ({ tag: 'Pair', fst, snd, type });
export interface ElimSigma { readonly tag: 'ElimSigma'; readonly usage: Usage; readonly motive: Core; readonly scrut: Core, readonly cas: Core }
export const ElimSigma = (usage: Usage, motive: Core, scrut: Core, cas: Core): ElimSigma => ({ tag: 'ElimSigma', usage, motive, scrut, cas });
export interface Proj { readonly tag: 'Proj'; readonly term: Core; readonly proj: ProjType }
export const Proj = (term: Core, proj: ProjType): Proj => ({ tag: 'Proj', term, proj });
export interface PropEq { readonly tag: 'PropEq'; readonly type: Core; readonly left: Core; readonly right: Core }
export const PropEq = (type: Core, left: Core, right: Core): PropEq => ({ tag: 'PropEq', type, left, right });
export interface Refl { readonly tag: 'Refl'; readonly type: Core; readonly val: Core };
export const Refl = (type: Core, val: Core): Refl => ({ tag: 'Refl', type, val });

export type ProjType = PProj | PIndex;

export interface PProj { readonly tag: 'PProj'; readonly proj: 'fst' | 'snd' }
export const PProj = (proj: 'fst' | 'snd'): PProj => ({ tag: 'PProj', proj });
export const PFst = PProj('fst');
export const PSnd = PProj('snd');
export interface PIndex { readonly tag: 'PIndex'; readonly name: Name | null; readonly index: Ix }
export const PIndex = (name: Name | null, index: Ix): PIndex => ({ tag: 'PIndex', name, index });

export const flattenPi = (t: Core): [[Usage, Mode, Name, Core][], Core] => {
  const params: [Usage, Mode, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Pi') {
    params.push([c.usage, c.mode, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenAbs = (t: Core): [[Usage, Mode, Name, Core][], Core] => {
  const params: [Usage, Mode, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Abs') {
    params.push([c.usage, c.mode, c.name, c.type]);
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
export const flattenSigma = (t: Core): [[Usage, Name, Core][], Core] => {
  const params: [Usage, Name, Core][] = [];
  let c = t;  
  while (c.tag === 'Sigma') {
    params.push([c.usage, c.name, c.type]);
    c = c.body;
  }
  return [params, c];
};
export const flattenPair = (t: Core): Core[] => {
  const r: Core[] = [];
  while (t.tag === 'Pair') {
    r.push(t.fst);
    t = t.snd;
  }
  r.push(t);
  return r;
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
const isSimple = (t: Core) => t.tag === 'Type' || t.tag === 'Var' || t.tag === 'Global' || t.tag === 'Proj';
const showS = (t: Core) => showP(!isSimple(t), t);
const showProjType = (p: ProjType): string => {
  if (p.tag === 'PProj') return p.proj === 'fst' ? '_1' : '_2';
  if (p.tag === 'PIndex') return p.name ? `${p.name}` : `${p.index}`;
  return p;
};
export const show = (t: Core): string => {
  if (t.tag === 'Type') return 'Type';
  if (t.tag === 'Var') return `${t.index}`;
  if (t.tag === 'Global') return `${t.name}`;
  if (t.tag === 'Pi') {
    const [params, ret] = flattenPi(t);
    return `${params.map(([u, m, x, t]) => u === many && m.tag === 'Expl' && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Let', t) : `${m.tag === 'Expl' ? '(' : '{'}${u === many ? '' : `${u} `}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' -> ')} -> ${show(ret)}`;
  }
  if (t.tag === 'Abs') {
    const [params, body] = flattenAbs(t);
    return `\\${params.map(([u, m, x, t]) => `${m.tag === 'Expl' ? '(' : '{'}${u === many ? '' : `${u} `}${x} : ${show(t)}${m.tag === 'Expl' ? ')' : '}'}`).join(' ')}. ${show(body)}`;
  }
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    return `${showS(fn)} ${args.map(([m, a]) => m.tag === 'Expl' ? showS(a) : `{${show(a)}}`).join(' ')}`;
  }
  if (t.tag === 'Let')
    return `let ${t.usage === many ? '' : `${t.usage} `}${t.name} : ${showP(t.type.tag === 'Let', t.type)} = ${showP(t.val.tag === 'Let', t.val)}; ${show(t.body)}`;
  if (t.tag === 'Sigma') {
    const [params, ret] = flattenSigma(t);
    return `${params.map(([u, x, t]) => u === many && x === '_' ? showP(t.tag === 'Pi' || t.tag === 'Sigma' || t.tag === 'Let', t) : `(${u === many ? '' : `${u} `}${x} : ${show(t)})`).join(' ** ')} ** ${show(ret)}`;
  }
  if (t.tag === 'Pair') {
    const ps = flattenPair(t);
    return `(${ps.map(t => show(t)).join(', ')} : ${show(t.type)})`;
  }
  if (t.tag === 'ElimSigma')
    return `elimSigma ${t.usage === many ? '' : `${t.usage} `}${showS(t.motive)} ${showS(t.scrut)} ${showS(t.cas)}`;
  if (t.tag === 'Proj') {
    const [hd, ps] = flattenProj(t);
    return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
  }
  if (t.tag === 'PropEq')
    return `{${show(t.type)}} ${show(t.left)} = ${show(t.right)}`;
  if (t.tag === 'Refl') return `Refl {${show(t.type)}} {${show(t.val)}}`;
  return t;
};

export const shift = (d: Ix, c: Ix, t: Core): Core => {
  if (t.tag === 'Var') return t.index < c ? t : Var(t.index + d);
  if (t.tag === 'Global') return t;
  if (t.tag === 'App') return App(shift(d, c, t.fn), t.mode, shift(d, c, t.arg));
  if (t.tag === 'Abs') return Abs(t.usage, t.mode, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Pair') return Pair(shift(d, c, t.fst), shift(d, c, t.snd), shift(d, c, t.type));
  if (t.tag === 'Proj') return Proj(shift(d, c, t.term), t.proj);
  if (t.tag === 'Let') return Let(t.usage, t.name, shift(d, c, t.type), shift(d, c, t.val), shift(d, c + 1, t.body));
  if (t.tag === 'Pi') return Pi(t.usage, t.mode, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'Sigma') return Sigma(t.usage, t.name, shift(d, c, t.type), shift(d, c + 1, t.body));
  if (t.tag === 'ElimSigma') return ElimSigma(t.usage, shift(d, c, t.motive), shift(d, c, t.scrut), shift(d, c, t.cas));
  if (t.tag === 'PropEq') return PropEq(shift(d, c, t.type), shift(d, c, t.left), shift(d, c, t.right));
  if (t.tag === 'Refl') return Refl(shift(d, c, t.type), shift(d, c, t.val));
  return t;
};

export const substVar = (j: Ix, s: Core, t: Core): Core => {
  if (t.tag === 'Var') return t.index === j ? s : t;
  if (t.tag === 'Global') return t;
  if (t.tag === 'App') return App(substVar(j, s, t.fn), t.mode, substVar(j, s, t.arg));
  if (t.tag === 'Abs') return Abs(t.usage, t.mode, t.name, substVar(j, s, t.type), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'Pair') return Pair(substVar(j, s, t.fst), substVar(j, s, t.snd), substVar(j, s, t.type));
  if (t.tag === 'Proj') return Proj(substVar(j, s, t.term), t.proj);
  if (t.tag === 'Let') return Let(t.usage, t.name, substVar(j, s, t.type), substVar(j, s, t.val), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'Pi') return Pi(t.usage, t.mode, t.name, substVar(j, s, t.type), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'Sigma') return Sigma(t.usage, t.name, substVar(j, s, t.type), substVar(j + 1, shift(1, 0, s), t.body));
  if (t.tag === 'ElimSigma') return ElimSigma(t.usage, substVar(j, s, t.motive), substVar(j, s, t.scrut), substVar(j, s, t.cas));
  if (t.tag === 'PropEq') return PropEq(substVar(j, s, t.type), substVar(j, s, t.left), substVar(j, s, t.right));
  if (t.tag === 'Refl') return Refl(substVar(j, s, t.type), substVar(j, s, t.val));
  return t;
};

export const subst = (t: Core, u: Core): Core => shift(-1, 0, substVar(0, shift(1, 0, u), t));

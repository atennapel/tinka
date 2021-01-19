import { Ix, Name } from './names';
import { PrimElimName, PrimName } from './prims';

export type Erased =
  Var | Global | Let |
  Abs | App |
  Pair | Proj |
  Bool | ElimBool |
  ElimFix;

export interface Var { readonly tag: 'Var'; readonly index: Ix }
export const Var = (index: Ix): Var => ({ tag: 'Var', index });
export interface Global { readonly tag: 'Global'; readonly name: Name }
export const Global = (name: Name): Global => ({ tag: 'Global', name });
export interface Let { readonly tag: 'Let'; readonly val: Erased; readonly body: Erased }
export const Let = (val: Erased, body: Erased): Let => ({ tag: 'Let', val, body });
export interface Abs { readonly tag: 'Abs'; readonly body: Erased }
export const Abs = (body: Erased): Abs => ({ tag: 'Abs', body });
export interface App { readonly tag: 'App'; readonly fn: Erased; readonly arg: Erased }
export const App = (fn: Erased, arg: Erased): App => ({ tag: 'App', fn, arg });
export interface Pair { readonly tag: 'Pair'; readonly fst: Erased; readonly snd: Erased }
export const Pair = (fst: Erased, snd: Erased): Pair => ({ tag: 'Pair', fst, snd });
export interface Proj { readonly tag: 'Proj'; readonly term: Erased; readonly proj: ProjType }
export const Proj = (term: Erased, proj: ProjType): Proj => ({ tag: 'Proj', term, proj });
export interface Bool { readonly tag: 'Bool'; readonly value: boolean }
export const Bool = (value: boolean): Bool => ({ tag: 'Bool', value });
export interface ElimBool { readonly tag: 'ElimBool'; readonly term: Erased; readonly ifTrue: Erased; readonly ifFalse: Erased }
export const ElimBool = (term: Erased, ifTrue: Erased, ifFalse: Erased): ElimBool => ({ tag: 'ElimBool', term, ifTrue, ifFalse });
export interface ElimFix { readonly tag: 'ElimFix'; readonly term: Erased; readonly cas: Erased }
export const ElimFix = (term: Erased, cas: Erased): ElimFix => ({ tag: 'ElimFix', term, cas });

export const True = Bool(true);
export const False = Bool(false);

export type ProjType = PProj | PIndex;

export interface PProj { readonly tag: 'PProj'; readonly proj: 'fst' | 'snd' }
export const PProj = (proj: 'fst' | 'snd'): PProj => ({ tag: 'PProj', proj });
export const PFst = PProj('fst');
export const PSnd = PProj('snd');
export interface PIndex { readonly tag: 'PIndex'; readonly index: Ix }
export const PIndex = (index: Ix): PIndex => ({ tag: 'PIndex', index });

export const Type = False;
export const TODO = Global('TODO');

export const flattenApp = (t: Erased): [Erased, Erased[]] => {
  const args: Erased[] = [];
  let c = t;  
  while (c.tag === 'App') {
    args.push(c.arg);
    c = c.fn;
  }
  return [c, args.reverse()];
};
export const flattenPair = (t: Erased): Erased[] => {
  const r: Erased[] = [];
  while (t.tag === 'Pair') {
    r.push(t.fst);
    t = t.snd;
  }
  r.push(t);
  return r;
};
export const flattenProj = (t: Erased): [Erased, ProjType[]] => {
  const r: ProjType[] = [];
  while (t.tag === 'Proj') {
    r.push(t.proj);
    t = t.term;
  }
  return [t, r.reverse()];
};

const showP = (b: boolean, t: Erased) => b ? `(${show(t)})` : show(t);
const isSimple = (t: Erased) => t.tag === 'Var' || t.tag === 'Global' || t.tag === 'Proj' || t.tag === 'Bool';
const showS = (t: Erased) => showP(!isSimple(t), t);
const showProjType = (p: ProjType): string => {
  if (p.tag === 'PProj') return p.proj === 'fst' ? '_1' : '_2';
  if (p.tag === 'PIndex') return `${p.index}`;
  return p;
};
export const show = (t: Erased): string => {
  if (t.tag === 'Var') return `'${t.index}`;
  if (t.tag === 'Global') return `${t.name}`;
  if (t.tag === 'Bool') return t.value ? '1' : '0';
  if (t.tag === 'Abs') return `\\${show(t.body)}`;
  if (t.tag === 'App') {
    const [fn, args] = flattenApp(t);
    return `${showS(fn)} ${args.map(a => showS(a)).join(' ')}`;
  }
  if (t.tag === 'Let')
    return `let ${showP(t.val.tag === 'Let', t.val)}; ${show(t.body)}`;
  if (t.tag === 'Pair') {
    const ps = flattenPair(t);
    return `(${ps.map(t => show(t)).join(', ')})`;
  }
  if (t.tag === 'Proj') {
    const [hd, ps] = flattenProj(t);
    return `${showS(hd)}.${ps.map(showProjType).join('.')}`;
  }
  if (t.tag === 'ElimBool')
    return `if ${showS(t.term)} ${showS(t.ifTrue)} ${showS(t.ifFalse)}`;
  if (t.tag === 'ElimFix')
    return `rec ${showS(t.term)} ${showS(t.cas)}`;
  return t;
};

const idTerm = Abs(Var(0));

export const erasePrim = (x: PrimName): Erased => {
  if (x === '*') return False;
  if (x === 'False') return False;
  if (x === 'True') return True;
  if (x === 'ICon') return idTerm;
  return Type;
};

export const erasePrimElim = (x: PrimElimName, scrut: Erased, cases: Erased[]): Erased => {
  if (x === 'elimUnit') return cases[0];
  if (x === 'elimVoid') return scrut;
  if (x === 'elimPropEq') return cases[0];
  if (x === 'elimSigma') {
    if (scrut.tag === 'Pair')
      return App(App(cases[0], scrut.fst), scrut.snd);
    if (scrut.tag === 'Var' || scrut.tag === 'Global')
      return App(App(cases[0], Proj(scrut, PFst)), Proj(scrut, PSnd));
    return Let(scrut, App(App(cases[0], Proj(Var(0), PFst)), Proj(Var(0), PSnd)));
  }

  if (x === 'elimBool') {
    if (scrut.tag === 'Bool')
      return scrut.value ? cases[0] : cases[1];
    return ElimBool(scrut, cases[0], cases[1]);
  }
  if (x === 'elimIFix') return ElimFix(scrut, cases[0]);

  return x;
};

import { Abs, App, Bool, ElimBool, ElimFix, Erased, Pair, PIndex, Proj, ProjType, Var, show as showE } from './erased';
import { globalLoad } from './globals';
import { Ix, Lvl } from './names';
import { cons, List, nil } from './utils/List';
import { impossible, terr } from './utils/utils';

export type Elim = EApp | EProj | EElimBool | EElimFix;

export interface EApp { readonly tag: 'EApp'; readonly arg: Val }
export const EApp = (arg: Val): EApp => ({ tag: 'EApp', arg });
export interface EProj { readonly tag: 'EProj'; readonly proj: ProjType }
export const EProj = (proj: ProjType): EProj => ({ tag: 'EProj', proj });
export interface EElimBool { readonly tag: 'EElimBool'; readonly ifTrue: Val; readonly ifFalse: Val }
export const EElimBool = (ifTrue: Val, ifFalse: Val): EElimBool => ({ tag: 'EElimBool', ifTrue, ifFalse });
export interface EElimFix { readonly tag: 'EElimFix'; readonly cas: Val }
export const EElimFix = (cas: Val): EElimFix => ({ tag: 'EElimFix', cas });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VNe | VAbs | VPair | VBool;

export interface VNe { readonly tag: 'VNe'; readonly head: Ix; readonly spine: Spine }
export const VNe = (head: Ix, spine: Spine): VNe => ({ tag: 'VNe', head, spine });
export interface VAbs { readonly tag: 'VAbs'; readonly clos: Clos }
export const VAbs = (clos: Clos): VAbs => ({ tag: 'VAbs', clos });
export interface VPair { readonly tag: 'VPair'; readonly fst: Val; readonly snd: Val }
export const VPair = (fst: Val, snd: Val): VPair => ({ tag: 'VPair', fst, snd });
export interface VBool { readonly tag: 'VBool'; readonly value: boolean }
export const VBool = (value: boolean): VBool => ({ tag: 'VBool', value });

export type ValWithClosure = Val & { tag: 'VAbs' };

export const VVar = (level: Lvl, spine: Spine = nil): Val => VNe(level, spine);

export const vinst = (val: ValWithClosure, arg: Val): Val => val.clos(arg);

export const vapp = (left: Val, right: Val): Val => {
  if (left.tag === 'VAbs') return vinst(left, right);
  if (left.tag === 'VNe') return VNe(left.head, cons(EApp(right), left.spine));
  return impossible(`vapp: ${left.tag}`);
};
export const vproj = (scrut: Val, proj: ProjType): Val => {
  if (scrut.tag === 'VPair') {
    if (proj.tag === 'PProj') return proj.proj === 'fst' ? scrut.fst : scrut.snd;
    if (proj.tag === 'PIndex') {
      if (proj.index === 0) return scrut.fst;
      return vproj(scrut.snd, PIndex(proj.index - 1));
    }
    return proj;
  }
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EProj(proj), scrut.spine));
  return impossible(`vproj: ${scrut.tag}`);
};
export const velimbool = (scrut: Val, ifTrue: Val, ifFalse: Val): Val => {
  if (scrut.tag === 'VBool') return scrut.value ? ifTrue : ifFalse;
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EElimBool(ifTrue, ifFalse), scrut.spine));
  return impossible(`velimbool: ${scrut.tag}`);
};
export const velimfix = (scrut: Val, cas: Val): Val => {
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EElimFix(cas), scrut.spine));
  return vapp(vapp(cas, VAbs(v => velimfix(v, cas))), scrut);
};

export const evaluate = (t: Erased, vs: EnvV): Val => {
  if (t.tag === 'Abs')
    return VAbs(v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Var') {
    const v = vs.index(t.index) || impossible(`evaluate: var ${t.index} has no value`);
    return v;
  }
  if (t.tag === 'Global') {
    const e = globalLoad(t.name);
    if (!e) return terr(`failed to load global ${t.name}`);
    return e.erval;
  }
  if (t.tag === 'App')
    return vapp(evaluate(t.fn, vs), evaluate(t.arg, vs));
  if (t.tag === 'Let')
    return evaluate(t.body, cons(evaluate(t.val, vs), vs));
  if (t.tag === 'Pair')
    return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs));
  if (t.tag === 'Proj')
    return vproj(evaluate(t.term, vs), t.proj);
  if (t.tag === 'Bool') return VBool(t.value);
  if (t.tag === 'ElimBool') return velimbool(evaluate(t.term, vs), evaluate(t.ifTrue, vs), evaluate(t.ifFalse, vs));
  if (t.tag === 'ElimFix') return velimfix(evaluate(t.term, vs), evaluate(t.cas, vs));
  return t;
};

const quoteHead = (h: Ix, k: Lvl): Erased => Var(k - (h + 1));
const quoteElim = (t: Erased, e: Elim, k: Lvl): Erased => {
  if (e.tag === 'EApp') return App(t, quote(e.arg, k));
  if (e.tag === 'EProj') return Proj(t, e.proj);
  if (e.tag === 'EElimBool') return ElimBool(t, quote(e.ifTrue, k), quote(e.ifFalse, k));
  if (e.tag === 'EElimFix') return ElimFix(t, quote(e.cas, k));
  return e;
};
export const quote = (v: Val, k: Lvl): Erased => {
  if (v.tag === 'VNe')
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k),
      quoteHead(v.head, k),
    );
  if (v.tag === 'VAbs')
    return Abs(quote(vinst(v, VVar(k)), k + 1));
  if (v.tag === 'VPair')
    return Pair(quote(v.fst, k), quote(v.snd, k));
  if (v.tag === 'VBool') return Bool(v.value);
  return v;
};

export const normalize = (t: Erased, k: Lvl = 0, vs: EnvV = nil): Erased => quote(evaluate(t, vs), k);
export const show = (v: Val, k: Lvl = 0): string => showE(quote(v, k));

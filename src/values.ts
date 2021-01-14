import { Abs, App, Core, Global, Pi, Var, show as showCore, Sigma, Pair, ElimSigma, Proj, ProjType, PIndex, PropEq, Refl, ElimPropEq, Prim, ElimBool, ElimVoid, ElimUnit } from './core';
import { globalLoad } from './globals';
import { Expl, Mode } from './mode';
import { Lvl, Name } from './names';
import { PrimName } from './prims';
import { Usage } from './usage';
import { Lazy } from './utils/Lazy';
import { cons, List, Nil, nil } from './utils/List';
import { impossible, terr } from './utils/utils';

export type Head = HVar | HPrim;

export interface HVar { readonly tag: 'HVar'; readonly level: Lvl }
export const HVar = (level: Lvl): HVar => ({ tag: 'HVar', level });
export interface HPrim { readonly tag: 'HPrim'; readonly name: PrimName }
export const HPrim = (name: PrimName): HPrim => ({ tag: 'HPrim', name });

export type Elim = EApp | EElimSigma | EProj | EElimPropEq | EElimVoid | EElimUnit | EElimBool;

export interface EApp { readonly tag: 'EApp'; readonly mode: Mode; readonly arg: Val }
export const EApp = (mode: Mode, arg: Val): EApp => ({ tag: 'EApp', mode, arg });
export interface EElimSigma { readonly tag: 'EElimSigma'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EElimSigma = (usage: Usage, motive: Val, cas: Val): EElimSigma => ({ tag: 'EElimSigma', usage, motive, cas });
export interface EProj { readonly tag: 'EProj'; readonly proj: ProjType }
export const EProj = (proj: ProjType): EProj => ({ tag: 'EProj', proj });
export interface EElimPropEq { readonly tag: 'EElimPropEq'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EElimPropEq = (usage: Usage, motive: Val, cas: Val): EElimPropEq => ({ tag: 'EElimPropEq', usage, motive, cas });
export interface EElimBool { readonly tag: 'EElimBool'; readonly usage: Usage; readonly motive: Val; readonly trueBranch: Val; readonly falseBranch: Val }
export const EElimBool = (usage: Usage, motive: Val, trueBranch: Val, falseBranch: Val): EElimBool => ({ tag: 'EElimBool', usage, motive, trueBranch, falseBranch });
export interface EElimUnit { readonly tag: 'EElimUnit'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EElimUnit = (usage: Usage, motive: Val, cas: Val): EElimUnit => ({ tag: 'EElimUnit', usage, motive, cas });
export interface EElimVoid { readonly tag: 'EElimVoid'; readonly usage: Usage; readonly motive: Val }
export const EElimVoid = (usage: Usage, motive: Val): EElimVoid => ({ tag: 'EElimVoid', usage, motive });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VNe | VGlobal | VAbs | VPi | VSigma | VPair | VPropEq | VRefl;

export interface VNe { readonly tag: 'VNe'; readonly head: Head; readonly spine: Spine }
export const VNe = (head: Head, spine: Spine): VNe => ({ tag: 'VNe', head, spine });
export interface VGlobal { readonly tag: 'VGlobal'; readonly head: Name; readonly spine: Spine; readonly val: Lazy<Val> };
export const VGlobal = (head: Name, spine: Spine, val: Lazy<Val>): VGlobal => ({ tag: 'VGlobal', head, spine, val });
export interface VAbs { readonly tag: 'VAbs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VAbs = (usage: Usage, mode: Mode, name: Name, type: Val, clos: Clos): VAbs => ({ tag: 'VAbs', usage, mode, name, type, clos });
export interface VPi { readonly tag: 'VPi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VPi = (usage: Usage, mode: Mode, name: Name, type: Val, clos: Clos): VPi => ({ tag: 'VPi', usage, mode, name, type, clos });
export interface VSigma { readonly tag: 'VSigma'; readonly usage: Usage; readonly exclusive: boolean; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VSigma = (usage: Usage, exclusive: boolean, name: Name, type: Val, clos: Clos): VSigma => ({ tag: 'VSigma', usage, exclusive, name, type, clos });
export interface VPair { readonly tag: 'VPair'; readonly fst: Val; readonly snd: Val; readonly type: Val }
export const VPair = (fst: Val, snd: Val, type: Val): VPair => ({ tag: 'VPair', fst, snd, type });
export interface VPropEq { readonly tag: 'VPropEq'; readonly type: Val; readonly left: Val; readonly right: Val }
export const VPropEq = (type: Val, left: Val, right: Val): VPropEq => ({ tag: 'VPropEq', type, left, right });
export interface VRefl { readonly tag: 'VRefl'; readonly type: Val; readonly val: Val }
export const VRefl = (type: Val, val: Val): VRefl => ({ tag: 'VRefl', type, val });

export type ValWithClosure = Val & { tag: 'VAbs' | 'VPi' | 'VSigma' };

export const VVar = (level: Lvl, spine: Spine = nil): Val => VNe(HVar(level), spine);
export const VPrim = (name: PrimName, spine: Spine = nil): Val => VNe(HPrim(name), spine);

export const VType = VPrim('Type');
export const VVoid = VPrim('Void');
export const VUnitType = VPrim('()');
export const VUnit = VPrim('*');
export const VBool = VPrim('Bool');
export const VTrue = VPrim('True');
export const VFalse = VPrim('False');

export const isVUnit = (v: Val): v is VNe & { head: HPrim & { name: '*' }, spine: Nil } =>
  v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === '*' && v.spine.isNil();
export const isVTrue = (v: Val): v is VNe & { head: HPrim & { name: 'True' }, spine: Nil } =>
  v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === 'True' && v.spine.isNil();
export const isVFalse = (v: Val): v is VNe & { head: HPrim & { name: 'False' }, spine: Nil } =>
  v.tag === 'VNe' && v.head.tag === 'HPrim' && v.head.name === 'False' && v.spine.isNil();

export const vinst = (val: ValWithClosure, arg: Val): Val => val.clos(arg);

export const force = (v: Val): Val => {
  if (v.tag === 'VGlobal') return force(v.val.get());
  return v;
};

export const vapp = (left: Val, mode: Mode, right: Val): Val => {
  if (left.tag === 'VAbs') return vinst(left, right);
  if (left.tag === 'VNe') return VNe(left.head, cons(EApp(mode, right), left.spine));
  if (left.tag === 'VGlobal') return VGlobal(left.head, cons(EApp(mode, right), left.spine), left.val.map(v => vapp(v, mode, right)));
  return impossible(`vapp: ${left.tag}`);
};
export const velimsigma = (usage: Usage, motive: Val, scrut: Val, cas: Val): Val => {
  if (scrut.tag === 'VPair') return vapp(vapp(cas, Expl, scrut.fst), Expl, scrut.snd);
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EElimSigma(usage, motive, cas), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EElimSigma(usage, motive, cas), scrut.spine), scrut.val.map(v => velimsigma(usage, motive, v, cas)));
  return impossible(`velimsigma: ${scrut.tag}`);
};
export const vproj = (scrut: Val, proj: ProjType): Val => {
  if (scrut.tag === 'VPair') {
    if (proj.tag === 'PProj') return proj.proj === 'fst' ? scrut.fst : scrut.snd;
    if (proj.tag === 'PIndex') {
      if (proj.index === 0) return scrut.fst;
      return vproj(scrut.snd, PIndex(proj.name, proj.index - 1));
    }
    return proj;
  }
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EProj(proj), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EProj(proj), scrut.spine), scrut.val.map(v => vproj(v, proj)));
  return impossible(`vproj: ${scrut.tag}`);
};
export const velimpropeq = (usage: Usage, motive: Val, scrut: Val, cas: Val): Val => {
  if (scrut.tag === 'VRefl') return vapp(cas, Expl, scrut.val);
  if (scrut.tag === 'VNe')
    return VNe(scrut.head, cons(EElimPropEq(usage, motive, cas), scrut.spine));
  if (scrut.tag === 'VGlobal')
    return VGlobal(scrut.head, cons(EElimPropEq(usage, motive, cas), scrut.spine), scrut.val.map(v => velimpropeq(usage, motive, v, cas)));
  return impossible(`velimpropeq: ${scrut.tag}`);
};
export const velimunit = (usage: Usage, motive: Val, scrut: Val, cas: Val): Val => {
  if (isVUnit(scrut)) return cas;
  if (scrut.tag === 'VNe')
    return VNe(scrut.head, cons(EElimUnit(usage, motive, cas), scrut.spine));
  if (scrut.tag === 'VGlobal')
    return VGlobal(scrut.head, cons(EElimUnit(usage, motive, cas), scrut.spine), scrut.val.map(v => velimunit(usage, motive, v, cas)));
  return impossible(`velimunit: ${scrut.tag}`);
};
export const velimvoid = (usage: Usage, motive: Val, scrut: Val): Val => {
  if (scrut.tag === 'VNe')
    return VNe(scrut.head, cons(EElimVoid(usage, motive), scrut.spine));
  if (scrut.tag === 'VGlobal')
    return VGlobal(scrut.head, cons(EElimVoid(usage, motive), scrut.spine), scrut.val.map(v => velimvoid(usage, motive, v)));
  return impossible(`velimvoid: ${scrut.tag}`);
};
export const velimbool = (usage: Usage, motive: Val, scrut: Val, trueBranch: Val, falseBranch: Val): Val => {
  if (isVTrue(scrut)) return trueBranch;
  if (isVFalse(scrut)) return falseBranch;
  if (scrut.tag === 'VNe')
    return VNe(scrut.head, cons(EElimBool(usage, motive, trueBranch, falseBranch), scrut.spine));
  if (scrut.tag === 'VGlobal')
    return VGlobal(scrut.head, cons(EElimBool(usage, motive, trueBranch, falseBranch), scrut.spine), scrut.val.map(v => velimbool(usage, motive, v, trueBranch, falseBranch)));
  return impossible(`velimbool: ${scrut.tag}`);
};

export const evaluate = (t: Core, vs: EnvV): Val => {
  if (t.tag === 'Abs')
    return VAbs(t.usage, t.mode, t.name, evaluate(t.type, vs), v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Pi')
    return VPi(t.usage, t.mode, t.name, evaluate(t.type, vs), v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Var') return vs.index(t.index) || impossible(`evaluate: var ${t.index} has no value`);
  if (t.tag === 'Global') return VGlobal(t.name, nil, Lazy.from(() => {
    const e = globalLoad(t.name);
    if (!e) return terr(`failed to load global ${t.name}`);
    return e.val;
  }));
  if (t.tag === 'Prim') return VPrim(t.name);
  if (t.tag === 'App')
    return vapp(evaluate(t.fn, vs), t.mode, evaluate(t.arg, vs));
  if (t.tag === 'Let')
    return evaluate(t.body, cons(evaluate(t.val, vs), vs));
  if (t.tag === 'Sigma')
    return VSigma(t.usage, t.exclusive, t.name, evaluate(t.type, vs), v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Pair')
    return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs), evaluate(t.type, vs));
  if (t.tag === 'ElimSigma')
    return velimsigma(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.cas, vs));
  if (t.tag === 'ElimPropEq')
    return velimpropeq(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.cas, vs));
  if (t.tag === 'ElimBool')
    return velimbool(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.trueBranch, vs), evaluate(t.falseBranch, vs));
  if (t.tag === 'Proj')
    return vproj(evaluate(t.term, vs), t.proj);
  if (t.tag === 'PropEq')
    return VPropEq(evaluate(t.type, vs), evaluate(t.left, vs), evaluate(t.right, vs));
  if (t.tag === 'Refl')
    return VRefl(evaluate(t.type, vs), evaluate(t.val, vs));
  if (t.tag === 'ElimUnit')
    return velimunit(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.cas, vs));
  if (t.tag === 'ElimVoid')
    return velimvoid(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs));
  return t;
};

const quoteHead = (h: Head, k: Lvl): Core => {
  if (h.tag === 'HVar') return Var(k - (h.level + 1));
  if (h.tag === 'HPrim') return Prim(h.name);
  return h;
};
const quoteElim = (t: Core, e: Elim, k: Lvl, full: boolean): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, quote(e.arg, k, full));
  if (e.tag === 'EElimSigma') return ElimSigma(e.usage, quote(e.motive, k, full), t, quote(e.cas, k, full));
  if (e.tag === 'EElimPropEq') return ElimPropEq(e.usage, quote(e.motive, k, full), t, quote(e.cas, k, full));
  if (e.tag === 'EProj') return Proj(t, e.proj);
  if (e.tag === 'EElimBool') return ElimBool(e.usage, quote(e.motive, k, full), t, quote(e.trueBranch, k, full), quote(e.falseBranch, k, full));
  if (e.tag === 'EElimUnit') return ElimUnit(e.usage, quote(e.motive, k, full), t, quote(e.cas, k, full));
  if (e.tag === 'EElimVoid') return ElimVoid(e.usage, quote(e.motive, k, full), t);
  return e;
};
export const quote = (v: Val, k: Lvl, full: boolean = false): Core => {
  if (v.tag === 'VNe')
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full),
      quoteHead(v.head, k),
    );
  if (v.tag === 'VGlobal') {
    if (full) return quote(v.val.get(), k, full);
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full),
      Global(v.head) as Core,
    );
  }
  if (v.tag === 'VAbs')
    return Abs(v.usage, v.mode, v.name, quote(v.type, k, full), quote(vinst(v, VVar(k)), k + 1, full));
  if (v.tag === 'VPi')
    return Pi(v.usage, v.mode, v.name, quote(v.type, k, full), quote(vinst(v, VVar(k)), k + 1, full));
  if (v.tag === 'VSigma')
    return Sigma(v.usage, v.exclusive, v.name, quote(v.type, k, full), quote(vinst(v, VVar(k)), k + 1, full));
  if (v.tag === 'VPair')
    return Pair(quote(v.fst, k, full), quote(v.snd, k, full), quote(v.type, k, full));
  if (v.tag === 'VPropEq')
    return PropEq(quote(v.type, k, full), quote(v.left, k, full), quote(v.right, k, full));
  if (v.tag === 'VRefl')
    return Refl(quote(v.type, k, full), quote(v.val, k, full));
  return v;
};

export const normalize = (t: Core, k: Lvl = 0, vs: EnvV = nil, full: boolean = false): Core => quote(evaluate(t, vs), k, full);
export const show = (v: Val, k: Lvl = 0, full: boolean = false): string => showCore(quote(v, k, full));

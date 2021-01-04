import { Abs, App, Core, Global, Pi, Type, Var, show as showCore, Sigma, Pair, IndSigma, Proj, PSnd, PFst } from './core';
import { globalLoad } from './globals';
import { Expl, Mode } from './mode';
import { Lvl, Name } from './names';
import { Usage } from './usage';
import { Lazy } from './utils/Lazy';
import { cons, List, nil } from './utils/List';
import { impossible, terr } from './utils/utils';

export type Head = HVar;

export interface HVar { readonly tag: 'HVar'; readonly level: Lvl }
export const HVar = (level: Lvl): HVar => ({ tag: 'HVar', level });

export type Elim = EApp | EIndSigma | EProj;

export interface EApp { readonly tag: 'EApp'; readonly mode: Mode; readonly arg: Val }
export const EApp = (mode: Mode, arg: Val): EApp => ({ tag: 'EApp', mode, arg });
export interface EIndSigma { readonly tag: 'EIndSigma'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EIndSigma = (usage: Usage, motive: Val, cas: Val): EIndSigma => ({ tag: 'EIndSigma', usage, motive, cas });
export interface EProj { readonly tag: 'EProj'; readonly proj: 'fst' | 'snd' }
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VType | VNe | VGlobal | VAbs | VPi | VSigma | VPair;

export interface VType { readonly tag: 'VType' }
export const VType: VType = { tag: 'VType' };
export interface VNe { readonly tag: 'VNe'; readonly head: Head; readonly spine: Spine }
export const VNe = (head: Head, spine: Spine): VNe => ({ tag: 'VNe', head, spine });
export interface VGlobal { readonly tag: 'VGlobal'; readonly head: Name; readonly spine: Spine; readonly val: Lazy<Val> };
export const VGlobal = (head: Name, spine: Spine, val: Lazy<Val>): VGlobal => ({ tag: 'VGlobal', head, spine, val });
export interface VAbs { readonly tag: 'VAbs'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VAbs = (usage: Usage, mode: Mode, name: Name, type: Val, clos: Clos): VAbs => ({ tag: 'VAbs', usage, mode, name, type, clos });
export interface VPi { readonly tag: 'VPi'; readonly usage: Usage; readonly mode: Mode; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VPi = (usage: Usage, mode: Mode, name: Name, type: Val, clos: Clos): VPi => ({ tag: 'VPi', usage, mode, name, type, clos });
export interface VSigma { readonly tag: 'VSigma'; readonly usage: Usage; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VSigma = (usage: Usage, name: Name, type: Val, clos: Clos): VSigma => ({ tag: 'VSigma', usage, name, type, clos });
export interface VPair { readonly tag: 'VPair'; readonly fst: Val; readonly snd: Val; readonly type: Val }
export const VPair = (fst: Val, snd: Val, type: Val): VPair => ({ tag: 'VPair', fst, snd, type });

export type ValWithClosure = Val & { tag: 'VAbs' | 'VPi' | 'VSigma' };

export const VVar = (level: Lvl, spine: Spine = nil): Val => VNe(HVar(level), spine);

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
export const vindsigma = (usage: Usage, motive: Val, scrut: Val, cas: Val): Val => {
  if (scrut.tag === 'VPair') return vapp(vapp(cas, Expl, scrut.fst), Expl, scrut.snd);
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EIndSigma(usage, motive, cas), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EIndSigma(usage, motive, cas), scrut.spine), scrut.val.map(v => vindsigma(usage, motive, v, cas)));
  return impossible(`vindsigma: ${scrut.tag}`);
};
export const vproj = (scrut: Val, proj: 'fst' | 'snd'): Val => {
  if (scrut.tag === 'VPair') return proj === 'fst' ? scrut.fst : scrut.snd;
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EProj(proj), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EProj(proj), scrut.spine), scrut.val.map(v => vproj(v, proj)));
  return impossible(`vindsigma: ${scrut.tag}`);
};

export const evaluate = (t: Core, vs: EnvV): Val => {
  if (t.tag === 'Type') return VType;
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
  if (t.tag === 'App')
    return vapp(evaluate(t.fn, vs), t.mode, evaluate(t.arg, vs));
  if (t.tag === 'Let')
    return evaluate(t.body, cons(evaluate(t.val, vs), vs));
  if (t.tag === 'Sigma')
    return VSigma(t.usage, t.name, evaluate(t.type, vs), v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Pair')
    return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs), evaluate(t.type, vs));
  if (t.tag === 'IndSigma')
    return vindsigma(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.cas, vs));
  if (t.tag === 'Proj')
    return vproj(evaluate(t.term, vs), t.proj.proj);
  return t;
};

const quoteHead = (h: Head, k: Lvl): Core => {
  if (h.tag === 'HVar') return Var(k - (h.level + 1));
  return h.tag;
};
const quoteElim = (t: Core, e: Elim, k: Lvl, full: boolean): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, quote(e.arg, k, full));
  if (e.tag === 'EIndSigma') return IndSigma(e.usage, quote(e.motive, k), t, quote(e.cas, k));
  if (e.tag === 'EProj') return Proj(t, e.proj === 'fst' ? PFst : PSnd);
  return e;
};
export const quote = (v: Val, k: Lvl, full: boolean = false): Core => {
  if (v.tag === 'VType') return Type;
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
    return Sigma(v.usage, v.name, quote(v.type, k), quote(vinst(v, VVar(k)), k + 1));
  if (v.tag === 'VPair')
    return Pair(quote(v.fst, k), quote(v.snd, k), quote(v.type, k));
  return v;
};

export const normalize = (t: Core, vs: EnvV = nil, full: boolean = false): Core => quote(evaluate(t, vs), 0, full);
export const show = (v: Val, k: Lvl = 0, full: boolean = false): string => showCore(quote(v, k, full));

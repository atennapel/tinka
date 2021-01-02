import { Abs, App, Core, Global, Pi, Type, Var, show as showCore, Sigma, Pair, IndSigma } from './core';
import { Expl, Mode } from './mode';
import { Lvl, Name } from './names';
import { Usage } from './usage';
import { Lazy } from './utils/Lazy';
import { cons, List, nil } from './utils/List';
import { impossible } from './utils/utils';

export type Head = HVar;

export interface HVar { readonly tag: 'HVar'; readonly level: Lvl }
export const HVar = (level: Lvl): HVar => ({ tag: 'HVar', level });

export type Elim = EApp | EIndSigma;

export interface EApp { readonly tag: 'EApp'; readonly mode: Mode; readonly arg: Val }
export const EApp = (mode: Mode, arg: Val): EApp => ({ tag: 'EApp', mode, arg });
export interface EIndSigma { readonly tag: 'EIndSigma'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EIndSigma = (usage: Usage, motive: Val, cas: Val): EIndSigma => ({ tag: 'EIndSigma', usage, motive, cas });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VType | VNe | VGlobal | VLocal | VAbs | VPi | VSigma | VPair;

export interface VType { readonly tag: 'VType' }
export const VType: VType = { tag: 'VType' };
export interface VNe { readonly tag: 'VNe'; readonly head: Head; readonly spine: Spine }
export const VNe = (head: Head, spine: Spine): VNe => ({ tag: 'VNe', head, spine });
export interface VGlobal { readonly tag: 'VGlobal'; readonly head: Name; readonly spine: Spine; readonly val: Lazy<Val> };
export const VGlobal = (head: Name, spine: Spine, val: Lazy<Val>): VGlobal => ({ tag: 'VGlobal', head, spine, val });
export interface VLocal { readonly tag: 'VLocal'; readonly head: Lvl; readonly level: Lvl; readonly spine: Spine; readonly val: Lazy<Val> };
export const VLocal = (head: Lvl, level: Lvl, spine: Spine, val: Lazy<Val>): VLocal => ({ tag: 'VLocal', head, level, spine, val });
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
  if (v.tag === 'VLocal') return force(v.val.get());
  return v;
};

export const vapp = (left: Val, mode: Mode, right: Val): Val => {
  if (left.tag === 'VAbs') return vinst(left, right);
  if (left.tag === 'VNe') return VNe(left.head, cons(EApp(mode, right), left.spine));
  if (left.tag === 'VGlobal') return VGlobal(left.head, cons(EApp(mode, right), left.spine), left.val.map(v => vapp(v, mode, right)));
  if (left.tag === 'VLocal') return VLocal(left.head, left.level, cons(EApp(mode, right), left.spine), left.val.map(v => vapp(v, mode, right)));
  return impossible(`vapp: ${left.tag}`);
};
export const vindsigma = (usage: Usage, motive: Val, scrut: Val, cas: Val): Val => {
  if (scrut.tag === 'VPair') return vapp(vapp(cas, Expl, scrut.fst), Expl, scrut.snd);
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EIndSigma(usage, motive, cas), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EIndSigma(usage, motive, cas), scrut.spine), scrut.val.map(v => vindsigma(usage, motive, v, cas)));
  if (scrut.tag === 'VLocal') return VLocal(scrut.head, scrut.level, cons(EIndSigma(usage, motive, cas), scrut.spine), scrut.val.map(v => vindsigma(usage, motive, v, cas)));
  return impossible(`vindsigma: ${scrut.tag}`);
};

export const evaluate = (t: Core, vs: EnvV): Val => {
  if (t.tag === 'Type') return VType;
  if (t.tag === 'Abs')
    return VAbs(t.usage, t.mode, t.name, evaluate(t.type, vs), v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Pi')
    return VPi(t.usage, t.mode, t.name, evaluate(t.type, vs), v => evaluate(t.body, cons(v, vs)));
  if (t.tag === 'Var') {
    const val = vs.index(t.index) || impossible(`evaluate: var ${t.index} has no value`);
    return VLocal(t.index, vs.length(), nil, Lazy.of(val));
  }
  if (t.tag === 'Global') return VGlobal(t.name, nil, Lazy.from(() => impossible('globals are not implemented yet'))); // TODO
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
  return t;
};

const quoteHead = (h: Head, k: Lvl): Core => {
  if (h.tag === 'HVar') return Var(k - (h.level + 1));
  return h.tag;
};
const quoteElim = (t: Core, e: Elim, k: Lvl, full: boolean): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, quote(e.arg, k, full));
  if (e.tag === 'EIndSigma') return IndSigma(e.usage, quote(e.motive, k), t, quote(e.cas, k));
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
  if (v.tag === 'VLocal') {
    if (full || k !== v.level) return quote(v.val.get(), k, full);
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full),
      Var(v.head) as Core,
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

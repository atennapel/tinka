import { Abs, App, Core, Global, Pi, Type, Var, show as showCore, Sigma, Pair, ElimSigma, Proj, ProjType, PIndex, PropEq, Refl, ElimPropEq, Nat, NatS, NatLit, ElimNat } from './core';
import { globalLoad } from './globals';
import { Expl, Mode } from './mode';
import { Lvl, Name } from './names';
import { many, Usage } from './usage';
import { Lazy } from './utils/Lazy';
import { cons, List, nil } from './utils/List';
import { impossible, terr } from './utils/utils';

export type Head = HVar;

export interface HVar { readonly tag: 'HVar'; readonly level: Lvl }
export const HVar = (level: Lvl): HVar => ({ tag: 'HVar', level });

export type Elim = EApp | EElimSigma | EProj | EElimPropEq | ENatS | EElimNat;

export interface EApp { readonly tag: 'EApp'; readonly mode: Mode; readonly arg: Val }
export const EApp = (mode: Mode, arg: Val): EApp => ({ tag: 'EApp', mode, arg });
export interface EElimSigma { readonly tag: 'EElimSigma'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EElimSigma = (usage: Usage, motive: Val, cas: Val): EElimSigma => ({ tag: 'EElimSigma', usage, motive, cas });
export interface EProj { readonly tag: 'EProj'; readonly proj: ProjType }
export const EProj = (proj: ProjType): EProj => ({ tag: 'EProj', proj });
export interface EElimPropEq { readonly tag: 'EElimPropEq'; readonly usage: Usage; readonly motive: Val; readonly cas: Val }
export const EElimPropEq = (usage: Usage, motive: Val, cas: Val): EElimPropEq => ({ tag: 'EElimPropEq', usage, motive, cas });
export interface ENatS { readonly tag: 'ENatS' }
export const ENatS: ENatS = { tag: 'ENatS' };
export interface EElimNat { readonly tag: 'EElimNat'; readonly usage: Usage; readonly motive: Val; readonly z: Val; readonly s: Val }
export const EElimNat = (usage: Usage, motive: Val, z: Val, s: Val): EElimNat => ({ tag: 'EElimNat', usage, motive, z, s });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VType | VNat | VNatLit | VNe | VGlobal | VAbs | VPi | VSigma | VPair | VPropEq | VRefl;

export interface VType { readonly tag: 'VType' }
export const VType: VType = { tag: 'VType' };
export interface VNat { readonly tag: 'VNat' }
export const VNat: VNat = { tag: 'VNat' };
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
export interface VPropEq { readonly tag: 'VPropEq'; readonly type: Val; readonly left: Val; readonly right: Val }
export const VPropEq = (type: Val, left: Val, right: Val): VPropEq => ({ tag: 'VPropEq', type, left, right });
export interface VRefl { readonly tag: 'VRefl'; readonly type: Val; readonly val: Val }
export const VRefl = (type: Val, val: Val): VRefl => ({ tag: 'VRefl', type, val });
export interface VNatLit { readonly tag: 'VNatLit'; readonly value: bigint }
export const VNatLit = (value: bigint): VNatLit => ({ tag: 'VNatLit', value });

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
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EElimPropEq(usage, motive, cas), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EElimPropEq(usage, motive, cas), scrut.spine), scrut.val.map(v => velimpropeq(usage, motive, v, cas)));
  return impossible(`velimpropeq: ${scrut.tag}`);
};
export const vnats = (scrut: Val): Val => {
  if (scrut.tag === 'VNatLit') return VNatLit(scrut.value + 1n);
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(ENatS, scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(ENatS, scrut.spine), scrut.val.map(v => vnats(v)));
  return impossible(`vnats: ${scrut.tag}`);
};
export const velimnat = (usage: Usage, motive: Val, scrut: Val, z: Val, s: Val): Val => {
  const m = vdecideS(scrut);
  if (m) return vapp(vapp(s, Expl, VAbs(many, Expl, 'm', VNat, m => velimnat(usage, motive, m, z, s))), Expl, m);
  if (scrut.tag === 'VNatLit' && scrut.value === 0n) return z;
  if (scrut.tag === 'VNe') return VNe(scrut.head, cons(EElimNat(usage, motive, z, s), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EElimNat(usage, motive, z, s), scrut.spine), scrut.val.map(v => velimnat(usage, motive, v, z, s)));
  return impossible(`velimnat: ${scrut.tag}`);
};

export const vdecideS = (v: Val): Val | null => {
  if (v.tag === 'VNatLit' && v.value > 0) return VNatLit(v.value - 1n);
  if (v.tag === 'VNe' && v.spine.isCons() && v.spine.head.tag === 'ENatS')
     return VNe(v.head, v.spine.tail);
  return null;
};

export const evaluate = (t: Core, vs: EnvV): Val => {
  if (t.tag === 'Type') return VType;
  if (t.tag === 'Nat') return VNat;
  if (t.tag === 'NatLit') return VNatLit(t.value);
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
  if (t.tag === 'ElimSigma')
    return velimsigma(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.cas, vs));
  if (t.tag === 'ElimPropEq')
    return velimpropeq(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.cas, vs));
  if (t.tag === 'Proj')
    return vproj(evaluate(t.term, vs), t.proj);
  if (t.tag === 'PropEq')
    return VPropEq(evaluate(t.type, vs), evaluate(t.left, vs), evaluate(t.right, vs));
  if (t.tag === 'Refl')
    return VRefl(evaluate(t.type, vs), evaluate(t.val, vs));
  if (t.tag === 'NatS')
    return vnats(evaluate(t.term, vs));
  if (t.tag == 'ElimNat')
    return velimnat(t.usage, evaluate(t.motive, vs), evaluate(t.scrut, vs), evaluate(t.z, vs), evaluate(t.s, vs));
  return t;
};

const quoteHead = (h: Head, k: Lvl): Core => {
  if (h.tag === 'HVar') return Var(k - (h.level + 1));
  return h.tag;
};
const quoteElim = (t: Core, e: Elim, k: Lvl, full: boolean): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, quote(e.arg, k, full));
  if (e.tag === 'EElimSigma') return ElimSigma(e.usage, quote(e.motive, k), t, quote(e.cas, k));
  if (e.tag === 'EElimPropEq') return ElimPropEq(e.usage, quote(e.motive, k), t, quote(e.cas, k));
  if (e.tag === 'EProj') return Proj(t, e.proj);
  if (e.tag === 'ENatS') return NatS(t);
  if (e.tag === 'EElimNat') return ElimNat(e.usage, quote(e.motive, k), t, quote(e.z, k), quote(e.s, k));
  return e;
};
export const quote = (v: Val, k: Lvl, full: boolean = false): Core => {
  if (v.tag === 'VType') return Type;
  if (v.tag === 'VNat') return Nat;
  if (v.tag === 'VNatLit') return NatLit(v.value);
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
  if (v.tag === 'VPropEq')
    return PropEq(quote(v.type, k), quote(v.left, k), quote(v.right, k));
  if (v.tag === 'VRefl')
    return Refl(quote(v.type, k), quote(v.val, k));
  return v;
};

export const normalize = (t: Core, vs: EnvV = nil, full: boolean = false): Core => quote(evaluate(t, vs), 0, full);
export const show = (v: Val, k: Lvl = 0, full: boolean = false): string => showCore(quote(v, k, full));

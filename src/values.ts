import { App, Core, Var, show as showCore, Abs, Pi, Global, Meta, Let, Sigma, Pair, Proj, ProjType, PIndex, Prim } from './core';
import { getMeta, MetaVar } from './metas';
import { Ix, Lvl, Name } from './names';
import { Lazy } from './utils/Lazy';
import { cons, List, Nil, nil } from './utils/List';
import { impossible } from './utils/utils';
import { getGlobal } from './globals';
import { PrimConName, PrimElimName } from './prims';
import { Erasure, Expl, Mode } from './mode';

export type Head = HVar | HPrim;

export interface HVar { readonly tag: 'HVar'; readonly level: Lvl }
export const HVar = (level: Lvl): HVar => ({ tag: 'HVar', level });
export interface HPrim { readonly tag: 'HPrim'; readonly name: PrimConName }
export const HPrim = (name: PrimConName): HPrim => ({ tag: 'HPrim', name });

export type GHead = HGlobal | HVar;

export interface HGlobal { readonly tag: 'HGlobal'; readonly name: Name }
export const HGlobal = (name: Name): HGlobal => ({ tag: 'HGlobal', name });

export type Elim = EApp | EProj | EPrim;

export interface EApp { readonly tag: 'EApp'; readonly mode: Mode; readonly arg: Val }
export const EApp = (mode: Mode, arg: Val): EApp => ({ tag: 'EApp', mode, arg });
export interface EProj { readonly tag: 'EProj'; readonly proj: ProjType }
export const EProj = (proj: ProjType): EProj => ({ tag: 'EProj', proj });
export interface EPrim { readonly tag: 'EPrim'; readonly name: PrimElimName; readonly args: Val[] }
export const EPrim = (name: PrimElimName, args: Val[]): EPrim => ({ tag: 'EPrim', name, args });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VRigid | VFlex | VGlobal | VAbs | VPi | VSigma | VPair;

export interface VRigid { readonly tag: 'VRigid'; readonly head: Head; readonly spine: Spine }
export const VRigid = (head: Head, spine: Spine): VRigid => ({ tag: 'VRigid', head, spine });
export interface VFlex { readonly tag: 'VFlex'; readonly head: MetaVar; readonly spine: Spine }
export const VFlex = (head: MetaVar, spine: Spine): VFlex => ({ tag: 'VFlex', head, spine });
export interface VGlobal { readonly tag: 'VGlobal'; readonly head: GHead; readonly spine: Spine; readonly val: Lazy<Val> };
export const VGlobal = (head: GHead, spine: Spine, val: Lazy<Val>): VGlobal => ({ tag: 'VGlobal', head, spine, val });
export interface VAbs { readonly tag: 'VAbs'; readonly erased: Erasure; readonly mode: Mode; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VAbs = (erased: Erasure, mode: Mode, name: Name, type: Val, clos: Clos): VAbs => ({ tag: 'VAbs', erased, mode, name, type, clos });
export interface VPi { readonly tag: 'VPi'; readonly erased: Erasure; readonly mode: Mode; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VPi = (erased: Erasure, mode: Mode, name: Name, type: Val, clos: Clos): VPi => ({ tag: 'VPi', erased, mode, name, type, clos });
export interface VSigma { readonly tag: 'VSigma'; readonly erased: Erasure; readonly name: Name; readonly type: Val; readonly clos: Clos }
export const VSigma = (erased: Erasure, name: Name, type: Val, clos: Clos): VSigma => ({ tag: 'VSigma', erased, name, type, clos });
export interface VPair { readonly tag: 'VPair'; readonly fst: Val; readonly snd: Val; readonly type: Val }
export const VPair = (fst: Val, snd: Val, type: Val): VPair => ({ tag: 'VPair', fst, snd, type });

export type ValWithClosure = Val & { tag: 'VAbs' | 'VPi' | 'VSigma' };
export const vinst = (val: ValWithClosure, arg: Val): Val => val.clos(arg);

export const VVar = (level: Lvl, spine: Spine = nil): Val => VRigid(HVar(level), spine);
export const VMeta = (meta: MetaVar, spine: Spine = nil): Val => VFlex(meta, spine);
export const VPrim = (name: PrimConName, spine: Spine = nil): Val => VRigid(HPrim(name), spine);

export const VType = VPrim('*');

export const isVVar = (v: Val): v is VRigid & { head: HVar, spine: Nil } =>
  v.tag === 'VRigid' && v.head.tag === 'HVar' && v.spine.isNil();

export const force = (v: Val, forceGlobal: boolean = true): Val => {
  if (v.tag === 'VGlobal' && forceGlobal) return force(v.val.get(), forceGlobal);
  if (v.tag === 'VFlex') {
    const e = getMeta(v.head);
    return e.tag === 'Solved' ? force(velimSpine(e.solution, v.spine), forceGlobal) : v;
  }
  return v;
};

export const velim = (e: Elim, t: Val): Val => {
  if (e.tag === 'EApp') return vapp(t, e.mode, e.arg);
  if (e.tag === 'EProj') return vproj(t, e.proj);
  if (e.tag === 'EPrim') return vprimelim(e.name, t, e.args);
  return e;
};

export const velimSpine = (t: Val, sp: Spine): Val => sp.foldr(velim, t);

export const vapp = (left: Val, mode: Mode, right: Val): Val => {
  if (left.tag === 'VAbs') return vinst(left, right); // TODO: erasure check?
  if (left.tag === 'VRigid') return VRigid(left.head, cons(EApp(mode, right), left.spine));
  if (left.tag === 'VFlex') return VFlex(left.head, cons(EApp(mode, right), left.spine));
  if (left.tag === 'VGlobal') return VGlobal(left.head, cons(EApp(mode, right), left.spine), left.val.map(v => vapp(v, mode, right)));
  return impossible(`vapp: ${left.tag}`);
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
  if (scrut.tag === 'VRigid') return VRigid(scrut.head, cons(EProj(proj), scrut.spine));
  if (scrut.tag === 'VFlex') return VFlex(scrut.head, cons(EProj(proj), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EProj(proj), scrut.spine), scrut.val.map(v => vproj(v, proj)));
  return impossible(`vproj: ${scrut.tag}`);
};
export const vprimelim = (name: PrimElimName, scrut: Val, args: Val[]): Val => {
  if (scrut.tag === 'VRigid') return VRigid(scrut.head, cons(EPrim(name, args), scrut.spine));
  if (scrut.tag === 'VFlex') return VFlex(scrut.head, cons(EPrim(name, args), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EPrim(name, args), scrut.spine), scrut.val.map(v => vprimelim(name, v, args)));
  return impossible(`vprimelim ${name}: ${scrut.tag}`);
};

export const velimBD = (env: EnvV, v: Val, s: List<[Mode, boolean]>): Val => {
  if (env.isNil() && s.isNil()) return v;
  if (env.isCons() && s.isCons())
    return s.head[1] ? vapp(velimBD(env.tail, v, s.tail), s.head[0], env.head) : velimBD(env.tail, v, s.tail);
  return impossible('velimBD');
};

export const evaluate = (t: Core, vs: EnvV, glueBefore: Ix = vs.length()): Val => {
  if (t.tag === 'Abs') return VAbs(t.erased, t.mode, t.name, evaluate(t.type, vs, glueBefore), v => evaluate(t.body, cons(v, vs), glueBefore));
  if (t.tag === 'Pi') return VPi(t.erased, t.mode, t.name, evaluate(t.type, vs, glueBefore), v => evaluate(t.body, cons(v, vs), glueBefore));
  if (t.tag === 'Sigma') return VSigma(t.erased, t.name, evaluate(t.type, vs, glueBefore), v => evaluate(t.body, cons(v, vs), glueBefore));
  if (t.tag === 'Meta') return VMeta(t.id);
  if (t.tag === 'InsertedMeta') return velimBD(vs, VMeta(t.id), t.spine);
  if (t.tag === 'App') return vapp(evaluate(t.fn, vs, glueBefore), t.mode, evaluate(t.arg, vs, glueBefore));
  if (t.tag === 'Pair') return VPair(evaluate(t.fst, vs, glueBefore), evaluate(t.snd, vs, glueBefore), evaluate(t.type, vs, glueBefore));
  if (t.tag === 'Let') return evaluate(t.body, cons(evaluate(t.val, vs, glueBefore), vs), glueBefore);
  if (t.tag === 'Proj') return vproj(evaluate(t.term, vs, glueBefore), t.proj);
  if (t.tag === 'Prim' && t.name === '*') return VType;
  if (t.tag === 'Var') {
    const v = vs.index(t.index) || impossible(`evaluate: var ${t.index} has no value`);
    const l = vs.length();
    if (t.index >= l - glueBefore) return VGlobal(HVar(l - t.index - 1), nil, Lazy.value(v));
    return v;
  }
  if (t.tag === 'Global') return VGlobal(HGlobal(t.name), nil, Lazy.from(() => {
    const e = getGlobal(t.name);
    if (!e) return impossible(`failed to load global ${t.name}`);
    return e.value;
  }));
  return t;
};

const quoteHead = (h: Head | GHead, k: Lvl): Core => {
  if (h.tag === 'HVar') return Var(k - (h.level + 1));
  if (h.tag === 'HPrim') return Prim(h.name);
  if (h.tag === 'HGlobal') return Global(h.name);
  return h;
};
const quoteElim = (t: Core, e: Elim, k: Lvl, full: boolean): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, quote(e.arg, k, full));
  if (e.tag === 'EProj') return Proj(t, e.proj);
  if (e.tag === 'EPrim') return App(e.args.map(v => quote(v, k, full)).reduce((x, y) => App(x, Expl, y), Prim(e.name) as Core), Expl, t);
  return e;
};
export const quote = (v_: Val, k: Lvl, full: boolean = false): Core => {
  const v = force(v_, false);
  if (v.tag === 'VRigid')
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full),
      quoteHead(v.head, k),
    );
  if (v.tag === 'VFlex')
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full),
      Meta(v.head) as Core,
    );
  if (v.tag === 'VGlobal') {
    if (full || v.head.tag === 'HVar' && v.head.level >= k) return quote(v.val.get(), k, full);
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full),
      quoteHead(v.head, k),
    );
  }
  if (v.tag === 'VAbs') return Abs(v.erased, v.mode, v.name, quote(v.type, k, full), quote(vinst(v, VVar(k)), k + 1, full));
  if (v.tag === 'VPi') return Pi(v.erased, v.mode, v.name, quote(v.type, k, full), quote(vinst(v, VVar(k)), k + 1, full));
  if (v.tag === 'VSigma') return Sigma(v.erased, v.name, quote(v.type, k, full), quote(vinst(v, VVar(k)), k + 1, full));
  if (v.tag === 'VPair') return Pair(quote(v.fst, k, full), quote(v.snd, k, full), quote(v.type, k, full));
  return v;
};

export const normalize = (t: Core, k: Lvl = 0, vs: EnvV = nil, full: boolean = false): Core => quote(evaluate(t, vs), k, full);
export const show = (v: Val, k: Lvl = 0, full: boolean = false): string => showCore(quote(v, k, full));

type S = [false, Val] | [true, Core];
const zonkSpine = (tm: Core, vs: EnvV, k: Lvl, full: boolean): S => {
  if (tm.tag === 'Meta') {
    const s = getMeta(tm.id);
    if (s.tag === 'Unsolved') return [true, zonk(tm, vs, k, full)];
    return [false, s.solution];
  }
  if (tm.tag === 'App') {
    const spine = zonkSpine(tm.fn, vs, k, full);
    return spine[0] ?
      [true, App(spine[1], tm.mode, zonk(tm.arg, vs, k, full))] :
      [false, vapp(spine[1], tm.mode, evaluate(tm.arg, vs))];
  }
  return [true, zonk(tm, vs, k, full)];
};
const vzonkBD = (env: EnvV, v: Val, s: List<[Mode, boolean]>): Val => {
  if (env.isNil() && s.isNil()) return v;
  if (env.isCons() && s.isCons())
    return s.head[1] ? vapp(vzonkBD(env.tail, v, s.tail), s.head[0], env.head) : vzonkBD(env.tail, v, s.tail);
  return impossible('vzonkBD');
};
export const zonk = (tm: Core, vs: EnvV = nil, k: Lvl = 0, full: boolean = false): Core => {
  if (tm.tag === 'Meta') {
    const s = getMeta(tm.id);
    if (s.tag === 'Unsolved') return tm;
    return quote(s.solution, k, full);
  }
  if (tm.tag === 'InsertedMeta') {
    const s = getMeta(tm.id);
    if (s.tag === 'Unsolved') return tm;
    return quote(vzonkBD(vs, s.solution, tm.spine), k, full);
  }
  if (tm.tag === 'Pi')
    return Pi(tm.erased, tm.mode, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, cons(VVar(k), vs), k + 1, full));
  if (tm.tag === 'Sigma')
    return Sigma(tm.erased, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, cons(VVar(k), vs), k + 1, full));
  if (tm.tag === 'Let')
    return Let(tm.erased, tm.name, zonk(tm.type, vs, k, full), zonk(tm.val, vs, k, full), zonk(tm.body, cons(VVar(k), vs), k + 1, full));
  if (tm.tag === 'Abs')
    return Abs(tm.erased, tm.mode, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, cons(VVar(k), vs), k + 1, full));
  if (tm.tag === 'App') {
    const spine = zonkSpine(tm.fn, vs, k, full);
    return spine[0] ?
      App(spine[1], tm.mode, zonk(tm.arg, vs, k, full)) :
      quote(vapp(spine[1], tm.mode, evaluate(tm.arg, vs)), k, full);
  }
  if (tm.tag === 'Pair') return Pair(zonk(tm.fst, vs, k, full), zonk(tm.snd, vs, k, full), zonk(tm.type, vs, k, full));
  if (tm.tag === 'Proj') return Proj(zonk(tm.term, vs, k, full), tm.proj);
  return tm;
};

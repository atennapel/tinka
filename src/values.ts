import { App, Core, Var, show as showCore, Abs, Pi, Global, Meta, Let, Sigma, Pair, Proj, ProjType, PIndex, Prim, NatLit, FinLit } from './core';
import { getMeta, MetaVar } from './metas';
import { Ix, Lvl, Name } from './names';
import { Lazy } from './utils/Lazy';
import { cons, List, Nil, nil } from './utils/List';
import { impossible } from './utils/utils';
import { getGlobal } from './globals';
import { PrimConName, PrimElimName } from './prims';
import { Erasure, Expl, Impl, Mode } from './mode';
import { config } from './config';

export type Head = HVar | HPrim;

export interface HVar { readonly tag: 'HVar'; readonly level: Lvl }
export const HVar = (level: Lvl): HVar => ({ tag: 'HVar', level });
export interface HPrim { readonly tag: 'HPrim'; readonly name: PrimConName }
export const HPrim = (name: PrimConName): HPrim => ({ tag: 'HPrim', name });

export type GHead = HGlobal | HLVar;

export interface HGlobal { readonly tag: 'HGlobal'; readonly name: Name }
export const HGlobal = (name: Name): HGlobal => ({ tag: 'HGlobal', name });
export interface HLVar { readonly tag: 'HLVar'; readonly level: Lvl }
export const HLVar = (level: Lvl): HLVar => ({ tag: 'HLVar', level });

export type Elim = EApp | EProj | EPrim;

export interface EApp { readonly tag: 'EApp'; readonly mode: Mode; readonly arg: Val }
export const EApp = (mode: Mode, arg: Val): EApp => ({ tag: 'EApp', mode, arg });
export interface EProj { readonly tag: 'EProj'; readonly proj: ProjType }
export const EProj = (proj: ProjType): EProj => ({ tag: 'EProj', proj });
export interface EPrim { readonly tag: 'EPrim'; readonly name: PrimElimName; readonly args: [Mode, Val][] }
export const EPrim = (name: PrimElimName, args: [Mode, Val][]): EPrim => ({ tag: 'EPrim', name, args });

export type Spine = List<Elim>;
export type EnvV = List<Val>;
export type Clos = (val: Val) => Val;

export type Val = VRigid | VFlex | VGlobal | VAbs | VPi | VSigma | VPair | VNatLit | VFinLit;

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
export interface VNatLit { readonly tag: 'VNatLit'; readonly value: bigint }
export const VNatLit = (value: bigint): VNatLit => ({ tag: 'VNatLit', value });
export interface VFinLit { readonly tag: 'VFinLit'; readonly value: bigint; readonly diff: Val; readonly type: Val }
export const VFinLit = (value: bigint, diff: Val, type: Val): VFinLit => ({ tag: 'VFinLit', value, diff, type });

export type ValWithClosure = Val & { tag: 'VAbs' | 'VPi' | 'VSigma' };
export const vinst = (val: ValWithClosure, arg: Val): Val => val.clos(arg);

export const VVar = (level: Lvl, spine: Spine = nil): Val => VRigid(HVar(level), spine);
export const VMeta = (meta: MetaVar, spine: Spine = nil): Val => VFlex(meta, spine);
export const VPrim = (name: PrimConName, spine: Spine = nil): Val => VRigid(HPrim(name), spine);

export const VType = VPrim('*');
export const VVoid = VPrim('Void');
export const VUnitType = VPrim('()');
export const VBool = VPrim('Bool');
export const VTrue = VPrim('True');
export const VFalse = VPrim('False');
export const VNat = VPrim('Nat');

export const VEq = (A: Val, x: Val, y: Val): Val => VPrim('Eq', List.of(EApp(Expl, y), EApp(Expl, x), EApp(Impl, A)));
export const VRefl = (A: Val, x: Val): Val => VPrim('Refl', List.of(EApp(Impl, x), EApp(Impl, A)));

// IData {I} F
export const VIDataPartial = (I: Val, F: Val): Val => VPrim('IData', List.of(EApp(Expl, F), EApp(Impl, I)));
// IData {I} F i
export const VIData = (I: Val, F: Val, i: Val): Val => VPrim('IData', List.of(EApp(Expl, i), EApp(Expl, F), EApp(Impl, I)));
// ICon {I} {F} {i} x
export const VICon = (I: Val, F: Val, i: Val, x: Val): Val => VPrim('ICon', List.of(EApp(Expl, x), EApp(Impl, i), EApp(Impl, F), EApp(Impl, I)));
export const VS = (n: Val): Val => vprimelim('S', n, []);
export const VFin = (n: Val): Val => VPrim('Fin', List.of(EApp(Expl, n)));
export const VFS = (k: Val, f: Val): Val => vprimelim('FS', f, [[Impl, k]]);

export const IxFun = (I: Val): Val => VPi(false, Expl, '_', I, _ => VType); // I -> *
export const IxFunctor = (I: Val): Val => VPi(false, Expl, '_', IxFun(I), _ => IxFun(I)); // (I -> *) -> I -> *

export const isVVar = (v: Val): v is VRigid & { head: HVar, spine: Nil } =>
  v.tag === 'VRigid' && v.head.tag === 'HVar' && v.spine.isNil();

export const getVPrim = (v: Val): [PrimConName, Val[]] | null => {
  if (v.tag === 'VRigid' && v.head.tag === 'HPrim') {
    const x = v.head.name;
    const args: Val[] = [];
    let allApps = true;
    v.spine.each(e => {
      if (e.tag !== 'EApp') {
        allApps = false;
        return;
      }
      args.push(e.arg);
    });
    if (!allApps) return null;
    return [x, args.reverse()];
  }
  return null;
};
export const isVNilary = (v: Val, x: Name): boolean => {
  const res = getVPrim(v);
  if (!res) return false;
  const [name, args] = res;
  return name === x && args.length === 0;
};
export const isVUnitType = (v: Val) => isVNilary(v, '()');
export const isVUnit = (v: Val) => isVNilary(v, '[]');

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
export const vapp2 = (f: Val, m1: Mode, a: Val, m2: Mode, b: Val): Val => vapp(vapp(f, m1, a), m2, b);
export const vapp3 = (f: Val, m1: Mode, a: Val, m2: Mode, b: Val, m3: Mode, c: Val): Val => vapp(vapp(vapp(f, m1, a), m2, b), m3, c);
export const vapp4 = (f: Val, m1: Mode, a: Val, m2: Mode, b: Val, m3: Mode, c: Val, m4: Mode, d: Val): Val => vapp(vapp(vapp(vapp(f, m1, a), m2, b), m3, c), m4, d);
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
export const vprimelim = (name: PrimElimName, scrut: Val, args: [Mode, Val][]): Val => {
  if (name === 'S' && scrut.tag === 'VNatLit') return VNatLit(scrut.value + 1n);
  if (name === 'FS' && scrut.tag === 'VFinLit') return VFinLit(scrut.value + 1n, scrut.diff, VS(scrut.type));
  if (name === 'elimNat' && scrut.tag === 'VNatLit') {
    if (scrut.value === 0n) return args[1][1];
    // elimNat P z s (m + 1) ~> s (\k. elimNat P z s k) m
    if (scrut.value > 0n) return vapp(vapp(args[2][1], Expl, VAbs(false, Expl, 'n', VNat, n => vprimelim('elimNat', n, args))), Expl, VNatLit(scrut.value - 1n));
  }
  if (name === 'elimFin' && scrut.tag === 'VFinLit') {
    // elimFin P z s {S n} (0/n) ~> z {n}
    if (scrut.value === 0n) return vapp(args[1][1], Impl, scrut.type);
    // elimFin P z s {S (S n)} (k/d/S n) ~> s (\{k} y. elimFin P z s {k} y) {S n} (k - 1/n)
    if (scrut.value > 0n)
      return vapp3(args[2][1], Expl, VAbs(true, Impl, 'k', VNat, k => VAbs(false, Expl, 'y', VFin(k), y => vprimelim('elimFin', y, args.slice(0, -1).concat([[Impl, k]])))), Impl, scrut.type, Expl, VFinLit(scrut.value - 1n, scrut.diff, vpred(scrut.type)));
  }
  if (name === 'weakenFin' && scrut.tag === 'VFinLit') {
    const m = args[0][1];
    return VFinLit(scrut.value, vaddFull(m, scrut.diff), vaddFull(m, scrut.type));
  }
  const res = getVPrim(scrut);
  if (res) {
    const [x, spine] = res;
    if (name === 'elimEq' && x === 'Refl') return vapp(args[2][1], Impl, spine[1]);
    if (name === 'axiomK' && x === 'Refl') return args[3][1];
    if (name === 'elimBool') {
      if (x === 'True') return args[1][1];
      if (x === 'False') return args[2][1];
    }
    // elimData {I} {F} P alg {i} (Con {I} {F} {i} x) ~> alg (\{-i : I} (z : Data {I} F i). elimData {I} {F} P alg {i} z) {i} x
    if (name === 'elimIData' && x === 'ICon') {
      const x = spine[3];
      const I = args[0][1];
      const F = args[1][1];
      const P = args[2][1];
      const alg = args[3][1];
      const i = args[4][1];
      const rec = VAbs(true, Impl, 'i', I, i => VAbs(false, Expl, 'z', VIData(I, F, i), z => vprimelim('elimIData', z, [[Impl, I], [Impl, F], [Expl, P], [Expl, alg], [Impl, i]])));
      return vapp3(alg, Expl, rec, Impl, i, Expl, x);
    }
  }
  if (name === 'elimNat' && (scrut.tag === 'VRigid' || scrut.tag === 'VFlex') && scrut.spine.isCons()) {
    const head = scrut.spine.head;
    if (head.tag === 'EPrim' && head.name === 'S') {
      const pred = scrut.tag === 'VRigid' ? VRigid(scrut.head, scrut.spine.tail) : VFlex(scrut.head, scrut.spine.tail);
      return vapp(vapp(args[2][1], Expl, VAbs(false, Expl, 'n', VNat, n => vprimelim('elimNat', n, args))), Expl, pred);
    }
  }
  if (name === 'elimFin' && (scrut.tag === 'VRigid' || scrut.tag === 'VFlex') && scrut.spine.isCons()) {
    const head = scrut.spine.head;
    if (head.tag === 'EPrim' && head.name === 'FS') {
      // elimFin P z s {S k} (FS {k} y) ~> s (\{k} y. elimFin P z s {k} y) {k} y
      const pred = scrut.tag === 'VRigid' ? VRigid(scrut.head, scrut.spine.tail) : VFlex(scrut.head, scrut.spine.tail);
      return vapp3(args[2][1], Expl, VAbs(true, Impl, 'k', VNat, k => VAbs(false, Expl, 'y', VFin(k), y => vprimelim('elimFin', y, args.slice(0, -1).concat([[Impl, k]])))), Impl, head.args[0][1], Expl, pred);
    }
  }
  if (name === 'weakenFin' && (scrut.tag === 'VRigid' || scrut.tag === 'VFlex') && scrut.spine.isCons()) {
    const m = args[0][1];
    const head = scrut.spine.head;
    if (head.tag === 'EPrim' && head.name === 'FS') {
      const n = head.args[0][1];
      const pred = scrut.tag === 'VRigid' ? VRigid(scrut.head, scrut.spine.tail) : VFlex(scrut.head, scrut.spine.tail);
      return VFS(vaddFull(m, n), vprimelim('weakenFin', pred, [[Impl, m], [Impl, vpred(n)]]));
    }
  }
  if (scrut.tag === 'VRigid') return VRigid(scrut.head, cons(EPrim(name, args), scrut.spine));
  if (scrut.tag === 'VFlex') return VFlex(scrut.head, cons(EPrim(name, args), scrut.spine));
  if (scrut.tag === 'VGlobal') return VGlobal(scrut.head, cons(EPrim(name, args), scrut.spine), scrut.val.map(v => vprimelim(name, v, args)));
  return impossible(`vprimelim ${name}: ${scrut.tag}`);
};
export const vpred = (n: Val): Val =>
  vprimelim('elimNat', n, [
    [Expl, VAbs(false, Expl, '_', VNat, _ => VNat)],
    [Expl, VNatLit(0n)],
    [Expl, VAbs(false, Expl, '_', VPi(false, Expl, '_', VNat, _ => VNat), _ => VAbs(false, Expl, 'm', VNat, m => m))]
  ]);
export const vadd = (n: Val, m: bigint): Val => {
  for (let i = 0; i < m; i++) n = VS(n);
  return n;
};
// elimNat (\_. Nat) b (\rec m. S (rec m)) a
export const vaddFull = (a: Val, b: Val): Val =>
  vprimelim('elimNat', a, [[Expl, VAbs(false, Expl, '_', VNat, _ => VNat)], [Expl, b], [Expl, VAbs(false, Expl, 'rec', VPi(false, Expl, '_', VNat, _ => VNat), rec => VAbs(false, Expl, 'm', VNat, m => VS(vapp(rec, Expl, m))))]]);

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
  if (t.tag === 'NatLit') return VNatLit(t.value);
  if (t.tag === 'FinLit') return VFinLit(t.value, evaluate(t.diff, vs, glueBefore), evaluate(t.type, vs, glueBefore));
  if (t.tag === 'App') return vapp(evaluate(t.fn, vs, glueBefore), t.mode, evaluate(t.arg, vs, glueBefore));
  if (t.tag === 'Pair') return VPair(evaluate(t.fst, vs, glueBefore), evaluate(t.snd, vs, glueBefore), evaluate(t.type, vs, glueBefore));
  if (t.tag === 'Let') return evaluate(t.body, cons(evaluate(t.val, vs, glueBefore), vs), glueBefore);
  if (t.tag === 'Proj') return vproj(evaluate(t.term, vs, glueBefore), t.proj);
  if (t.tag === 'Var') {
    const v = vs.index(t.index) || impossible(`evaluate: var ${t.index} has no value`);
    const l = vs.length();
    const i = t.index;
    if (i >= l - glueBefore) return VGlobal(HLVar(l - i - 1), nil, Lazy.value(v));
    return v;
  }
  if (t.tag === 'Global') return VGlobal(HGlobal(t.name), nil, Lazy.from(() => {
    const e = getGlobal(t.name);
    if (!e) return impossible(`failed to load global ${t.name}`);
    return e.value;
  }));
  if (t.tag === 'Prim') {
    if (t.name === 'elimEq')
      return VAbs(true, Impl, 'A', VType, A =>
        VAbs(true, Expl, 'P', VPi(false, Expl, 'x', A, x => VPi(false, Expl, 'y', A, y => VPi(false, Expl, '_', VEq(A, x, y), _ => VType))), P =>
        VAbs(false, Expl, 'q', VPi(true, Impl, 'x', A, x => vapp(vapp(vapp(P, Expl, x), Expl, x), Expl, VRefl(A, x))), q =>
        VAbs(true, Impl, 'x', A, x =>
        VAbs(true, Impl, 'y', A, y =>
        VAbs(false, Expl, 'p', VEq(A, x, y), p =>
        vprimelim('elimEq', p, [[Impl, A], [Expl, P], [Expl, q], [Impl, x], [Impl, y]])))))));
    if (t.name === 'absurd')
      return VAbs(true, Impl, 'A', VType, A => VAbs(false, Expl, 'v', VVoid, v => vprimelim('absurd', v, [[Impl, A]])));
    if (t.name === 'elimBool')
      return VAbs(true, Expl, 'P', VPi(false, Expl, '_', VBool, _ => VType), P =>
        VAbs(false, Expl, 't', vapp(P, Expl, VTrue), t =>
        VAbs(false, Expl, 'f', vapp(P, Expl, VFalse), f =>
        VAbs(false, Expl, 'b', VBool, b => vprimelim('elimBool', b, [[Expl, P], [Expl, t], [Expl, f]])))));
    if (t.name === 'elimIData')
      return VAbs(true, Impl, 'I', VType, I =>
        VAbs(true, Impl, 'F', IxFunctor(I), F =>
        VAbs(true, Expl, 'P', VPi(false, Impl, 'i', I, i => VPi(false, Expl, '_', VIData(I, F, i), _ => VType)), P =>
        VAbs(false, Expl, 'alg', VPi(false, Expl, '_', VPi(true, Impl, 'i', I, i => VPi(false, Expl, 'z', VIData(I, F, i), z => vapp2(P, Impl, i, Expl, z))), _ => VPi(true, Impl, 'i', I, i => VPi(false, Expl, 'y', vapp2(F, Expl, VIDataPartial(I, F), Expl, i), y => vapp2(P, Impl, i, Expl, VICon(I, F, i, y))))), alg =>
        VAbs(true, Impl, 'i', I, i =>
        VAbs(false, Expl, 'x', VIData(I, F, i), x =>
        vprimelim('elimIData', x, [[Impl, I], [Impl, F], [Expl, P], [Expl, alg], [Impl, i]])))))));
    if (t.name === 'S') return VAbs(false, Expl, 'n', VNat, n => vprimelim('S', n, []));
    if (t.name === 'elimNat')
      return VAbs(true, Expl, 'P', VPi(false, Expl, '_', VNat, _ => VType), P =>
        VAbs(false, Expl, 'z', vapp(P, Expl, VNatLit(0n)), z =>
        VAbs(false, Expl, 's', VPi(false, Expl, '_', VPi(false, Expl, 'k', VNat, k => vapp(P, Expl, k)), _ => VPi(false, Expl, 'm', VNat, m => vapp(P, Expl, VS(m)))), s =>
        VAbs(false, Expl, 'n', VNat, n => vprimelim('elimNat', n, [[Expl, P], [Expl, z], [Expl, s]])))));
    if (t.name === 'FS') return VAbs(true, Impl, 'n', VNat, n => VAbs(false, Expl, 'f', VFin(n), f => vprimelim('FS', f, [[Impl, n]])))
    if (t.name === 'elimFin')
      return VAbs(true, Expl, 'P', VPi(false, Expl, 'n', VNat, n => VPi(false, Expl, '_', VFin(n), _ => VType)), P =>
        VAbs(false, Expl, 'z', VPi(true, Impl, 'm', VNat, m => vapp2(P, Expl, VS(m), Expl, VFinLit(0n, m, m))), z =>
        VAbs(false, Expl, 's', VPi(false, Expl, '_', VPi(true, Impl, 'k', VNat, k => VPi(false, Expl, 'y', VFin(k), y => vapp2(P, Expl, k, Expl, y))), _ => VPi(true, Impl, 'k', VNat, k => VPi(false, Expl, 'y', VFin(k), y => vapp2(P, Expl, VS(k), Expl, VFS(k, y))))), s =>
        VAbs(true, Impl, 'n', VNat, n =>
        VAbs(false, Expl, 'x', VFin(n), x =>
        vprimelim('elimFin', x, [[Expl, P], [Expl, z], [Expl, s], [Impl, n]]))))));
    if (t.name === 'weakenFin')
      return VAbs(true, Impl, 'm', VNat, m => VAbs(true, Impl, 'n', VNat, n => VAbs(false, Expl, 'f', VFin(n), f => vprimelim('weakenFin', f, [[Impl, m], [Impl, n]]))));
    if (t.name === 'axiomK')
      return VAbs(true, Impl, 'A', VType, A =>
        VAbs(true, Impl, 'x', A, x =>
        VAbs(true, Expl, 'P', VPi(false, Expl, '_', VEq(A, x, x), _ => VType), P =>
        VAbs(false, Expl, 'p', vapp(P, Expl, VRefl(A, x)), p =>
        VAbs(false, Expl, 'h', VEq(A, x, x), h => vprimelim('axiomK', h, [[Impl, A], [Impl, x], [Expl, P], [Expl, p]]))))));
    return VPrim(t.name);
  }
  return t;
};

const localGlueEscaped = (k: Lvl, kBefore: Lvl, v: VGlobal): boolean => {
  const h = v.head;
  if (h.tag !== 'HLVar') return false;
  if (!config.localGlue) return true;
  return h.level >= kBefore;
};
const quoteHead = (h: Head | GHead, k: Lvl): Core => {
  if (h.tag === 'HVar') return Var(k - (h.level + 1));
  if (h.tag === 'HLVar') return Var(k - (h.level + 1));
  if (h.tag === 'HPrim') return Prim(h.name);
  if (h.tag === 'HGlobal') return Global(h.name);
  return h;
};
const quoteElim = (t: Core, e: Elim, k: Lvl, full: boolean, kBefore: Lvl): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, quote(e.arg, k, full, kBefore));
  if (e.tag === 'EProj') return Proj(t, e.proj);
  if (e.tag === 'EPrim') return App(e.args.reduce((x, [m, v]) => App(x, m, quote(v, k, full, kBefore)), Prim(e.name) as Core), Expl, t);
  return e;
};
export const quote = (v_: Val, k: Lvl, full: boolean = false, kBefore: Lvl = k): Core => {
  const v = force(v_, false);
  if (v.tag === 'VNatLit') return NatLit(v.value);
  if (v.tag === 'VFinLit') return FinLit(v.value, quote(v.diff, k, full, kBefore), quote(v.type, k, full, kBefore));
  if (v.tag === 'VRigid')
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full, kBefore),
      quoteHead(v.head, k),
    );
  if (v.tag === 'VFlex')
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full, kBefore),
      Meta(v.head) as Core,
    );
  if (v.tag === 'VGlobal') {
    if (full || localGlueEscaped(k, kBefore, v)) return quote(v.val.get(), k, full, kBefore);
    return v.spine.foldr(
      (x, y) => quoteElim(y, x, k, full, kBefore),
      quoteHead(v.head, k),
    );
  }
  if (v.tag === 'VAbs') return Abs(v.erased, v.mode, v.name, quote(v.type, k, full, kBefore), quote(vinst(v, VVar(k)), k + 1, full, kBefore));
  if (v.tag === 'VPi') return Pi(v.erased, v.mode, v.name, quote(v.type, k, full, kBefore), quote(vinst(v, VVar(k)), k + 1, full, kBefore));
  if (v.tag === 'VSigma') return Sigma(v.erased, v.name, quote(v.type, k, full, kBefore), quote(vinst(v, VVar(k)), k + 1, full, kBefore));
  if (v.tag === 'VPair') return Pair(quote(v.fst, k, full, kBefore), quote(v.snd, k, full, kBefore), quote(v.type, k, full, kBefore));
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

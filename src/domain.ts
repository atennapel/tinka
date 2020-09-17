import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pi, Global, showSurface, Meta, Let, Sigma, Pair, Prim, Proj, Sort, NatLit, FinLit } from './syntax';
import { impossible } from './utils/utils';
import { Lazy, mapLazy, forceLazy, lazyOf } from './utils/lazy';
import { Plicity, PrimName, Sorts } from './surface';
import { globalGet } from './globalenv';
import { metaGet } from './metas';

export type Head = HVar | HGlobal | HMeta | HPrim;

export type HVar = { tag: 'HVar', index: Ix };
export const HVar = (index: Ix): HVar => ({ tag: 'HVar', index });
export type HGlobal = { tag: 'HGlobal', name: Name };
export const HGlobal = (name: Name): HGlobal => ({ tag: 'HGlobal', name });
export type HMeta = { tag: 'HMeta', index: Ix };
export const HMeta = (index: Ix): HMeta => ({ tag: 'HMeta', index });
export type HPrim = { tag: 'HPrim', name: PrimName };
export const HPrim = (name: PrimName): HPrim => ({ tag: 'HPrim', name });

export type Elim = EApp | EProj | EElimHEq | EElimHEqUnsafe | ES | EFS | EIndNat | EIndFin | EIFixInd;

export type EApp = { tag: 'EApp', plicity: Plicity, arg: Val };
export const EApp = (plicity: Plicity, arg: Val): EApp => ({ tag: 'EApp', plicity, arg });
export type EProj = { tag: 'EProj', proj: 'fst' | 'snd' };
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });
export type EElimHEq = { tag: 'EElimHEq', args: Val[] };
export const EElimHEq = (args: Val[]): EElimHEq => ({ tag: 'EElimHEq', args });
export type EElimHEqUnsafe = { tag: 'EElimHEqUnsafe', args: Val[] };
export const EElimHEqUnsafe = (args: Val[]): EElimHEqUnsafe => ({ tag: 'EElimHEqUnsafe', args });
export type ES = { tag: 'ES' };
export const ES: ES = { tag: 'ES' };
export type EFS = { tag: 'EFS', type: Val };
export const EFS = (type: Val): EFS => ({ tag: 'EFS', type });
export type EIndNat = { tag: 'EIndNat', args: Val[] };
export const EIndNat = (args: Val[]): EIndNat => ({ tag: 'EIndNat', args });
export type EIndFin = { tag: 'EIndFin', args: Val[] };
export const EIndFin = (args: Val[]): EIndFin => ({ tag: 'EIndFin', args });
export type EIFixInd = { tag: 'EIFixInd', args: Val[] };
export const EIFixInd = (args: Val[]): EIFixInd => ({ tag: 'EIFixInd', args });

export type Clos = (val: Val) => Val;
export type Val = VNe | VGlued | VAbs | VPi | VSigma | VPair | VSort | VNatLit | VFinLit;

export type VNe = { tag: 'VNe', head: Head, args: List<Elim> };
export const VNe = (head: Head, args: List<Elim>): VNe => ({ tag: 'VNe', head, args });
export type VGlued = { tag: 'VGlued', head: Head, args: List<Elim>, val: Lazy<Val> };
export const VGlued = (head: Head, args: List<Elim>, val: Lazy<Val>): VGlued => ({ tag: 'VGlued', head, args, val });
export type VAbs = { tag: 'VAbs', plicity: Plicity, name: Name, type: Val, body: Clos };
export const VAbs = (plicity: Plicity, name: Name, type: Val, body: Clos): VAbs => ({ tag: 'VAbs', plicity, name, type, body});
export type VPi = { tag: 'VPi', plicity: Plicity, name: Name, type: Val, body: Clos };
export const VPi = (plicity: Plicity, name: Name, type: Val, body: Clos): VPi => ({ tag: 'VPi', plicity, name, type, body});
export type VSigma = { tag: 'VSigma', plicity: Plicity, plicity2: Plicity, name: Name, type: Val, body: Clos };
export const VSigma = (plicity: Plicity, plicity2: Plicity, name: Name, type: Val, body: Clos): VSigma => ({ tag: 'VSigma', plicity, plicity2, name, type, body});
export type VPair = { tag: 'VPair', plicity: Plicity, plicity2: Plicity, fst: Val, snd: Val, type: Val };
export const VPair = (plicity: Plicity, plicity2: Plicity, fst: Val, snd: Val, type: Val): VPair => ({ tag: 'VPair', plicity, plicity2, fst, snd, type });
export type VSort = { tag: 'VSort', sort: Sorts };
export const VSort = (sort: Sorts): VSort => ({ tag: 'VSort', sort });
export type VNatLit = { tag: 'VNatLit', val: bigint };
export const VNatLit = (val: bigint): VNatLit => ({ tag: 'VNatLit', val });
export type VFinLit = { tag: 'VFinLit', index: bigint, cap: Val };
export const VFinLit = (index: bigint, cap: Val): VFinLit => ({ tag: 'VFinLit', index, cap });

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);
export const VGlobal = (name: Name): VNe => VNe(HGlobal(name), Nil);
export const VMeta = (index: Ix): VNe => VNe(HMeta(index), Nil);
export const VPrim = (name: PrimName): VNe => VNe(HPrim(name), Nil);

export const VType = VSort('*');

export const VHEq = VPrim('HEq');
export const VIFix = VPrim('IFix');
export const VReflHEq = VPrim('ReflHEq');
export const vheq = (A: Val, B: Val, a: Val, b: Val) => vapp(vapp(vapp(vapp(VHEq, true, A), true, B), false, a), false, b);
export const VNat = VPrim('Nat');
export const VFin = VPrim('Fin');
export const VS = VPrim('S');

export type EnvV = List<Val>;
export const extendV = (vs: EnvV, val: Val): EnvV => Cons(val, vs);
export const showEnvV = (l: EnvV, k: Ix = 0, full: boolean = false): string => listToString(l, v => showTerm(quote(v, k, full)));

export const force = (v: Val): Val => {
  if (v.tag === 'VGlued') return force(forceLazy(v.val));
  if (v.tag === 'VNe' && v.head.tag === 'HMeta') {
    const val = metaGet(v.head.index);
    if (val.tag === 'Unsolved') return v;
    return force(foldr((elim, y) =>
      elim.tag === 'EProj' ? vproj(elim.proj, y) :
      elim.tag === 'EElimHEq' ? velimheq([y].concat(elim.args)) :
      elim.tag === 'EElimHEqUnsafe' ? velimhequnsafe([y].concat(elim.args)) :
      elim.tag === 'ES' ? vsucc(y) :
      elim.tag === 'EIndNat' ? vindnat([y].concat(elim.args)) :
      elim.tag === 'EFS' ? vfsucc(elim.type, y) :
      elim.tag === 'EIndFin' ? vindfin([y].concat(elim.args)) :
      elim.tag === 'EIFixInd' ? vifixind([y].concat(elim.args)) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};
export const forceGlue = (v: Val): Val => {
  if (v.tag === 'VNe' && v.head.tag === 'HMeta') {
    const val = metaGet(v.head.index);
    if (val.tag === 'Unsolved') return v;
    return forceGlue(foldr((elim, y) =>
      elim.tag === 'EProj' ? vproj(elim.proj, y) :
      elim.tag === 'EElimHEq' ? velimheq([y].concat(elim.args)) :
      elim.tag === 'EElimHEqUnsafe' ? velimhequnsafe([y].concat(elim.args)) :
      elim.tag === 'ES' ? vsucc(y) :
      elim.tag === 'EIndNat' ? vindnat([y].concat(elim.args)) :
      elim.tag === 'EFS' ? vfsucc(elim.type, y) :
      elim.tag === 'EIndFin' ? vindfin([y].concat(elim.args)) :
      elim.tag === 'EIFixInd' ? vifixind([y].concat(elim.args)) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};

export const vapp = (a: Val, plicity: Plicity, b: Val): Val => {
  if (a.tag === 'VAbs') {
    if (a.plicity !== plicity) {
      return impossible(`plicity mismatch in vapp`);
    }
    return a.body(b);
  }
  if (a.tag === 'VNe')
    return VNe(a.head, Cons(EApp(plicity, b), a.args));
  if (a.tag === 'VGlued')
    return VGlued(a.head, Cons(EApp(plicity, b), a.args), mapLazy(a.val, v => vapp(v, plicity, b)));
  return impossible(`vapp: ${a.tag}`);
};
export const vproj = (proj: 'fst' | 'snd', v: Val): Val => {
  if (v.tag === 'VPair') return proj === 'fst' ? v.fst : v.snd;
  if (v.tag === 'VNe') return VNe(v.head, Cons(EProj(proj), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EProj(proj), v.args), mapLazy(v.val, v => vproj(proj, v)));
  return impossible(`vsnd: ${v.tag}`);
};
export const velimheq = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'ReflHEq') {
      // elimHEq {A} {a} {P} q {b} (ReflHEq {A} {a}) ~> q 
      return rest[3];
    }
    return VNe(v.head, Cons(EElimHEq(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EElimHEq(rest), v.args), mapLazy(v.val, v => velimheq([v].concat(rest))));
  return impossible(`velimheq: ${v.tag}`);
};
export const velimhequnsafe = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'ReflHEq') {
      // elimHEq {A} {a} {P} q {b} {ReflHEq {A} {a}} ~> q 
      return rest[3];
    }
    return VNe(v.head, Cons(EElimHEqUnsafe(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EElimHEqUnsafe(rest), v.args), mapLazy(v.val, v => velimhequnsafe([v].concat(rest))));
  return impossible(`velimhequnsafe: ${v.tag}`);
};
export const vsucc = (v: Val): Val => {
  if (v.tag === 'VNatLit') return VNatLit(v.val + 1n);
  if (v.tag === 'VNe')
    return VNe(v.head, Cons(ES, v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(ES, v.args), mapLazy(v.val, v => vsucc(v)));
  return impossible(`vsucc: ${v.tag}`);
};
export const vindnat = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNatLit') {
    if (v.val === 0n) return rest[1];
    return vapp(vapp(rest[2], false, VAbs(false, 'k', VNat, k => vindnat([k].concat(rest)))), false, VNatLit(v.val - 1n));
  }
  if (v.tag === 'VNe') {
    if (v.args.tag === 'Cons' && v.args.head.tag === 'ES')
      return vapp(vapp(rest[2], false, VAbs(false, 'k', VNat, k => vindnat([k].concat(rest)))), false, VNe(v.head, v.args.tail));
    return VNe(v.head, Cons(EIndNat(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EIndNat(rest), v.args), mapLazy(v.val, v => vindnat([v].concat(rest))));
  return impossible(`vindnat: ${v.tag}`);
};
export const vfsucc = (type: Val, v: Val): Val => {
  if (v.tag === 'VFinLit') return VFinLit(v.index + 1n, vsucc(v.cap));
  if (v.tag === 'VNe')
    return VNe(v.head, Cons(EFS(type), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EFS(type), v.args), mapLazy(v.val, v => vfsucc(type, v)));
  return impossible(`vfsucc: ${v.tag}`);
};
export const vindfin = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VFinLit') {
    // genindFin {P} z s {S k} (0, k) ~> z {k}
    if (v.index === 0n) return vapp(rest[1], true, v.cap);
    const rest2 = rest.slice(0, -1);
    // genindFin {P} z s {S k} (n, k) ~> s (\{m : Nat} (f : Fin m). genindFin {P} z s {m} f) {k} (n - 1, k)
    return vapp(vapp(vapp(rest[2], false, VAbs(true, 'm', VNat, m => VAbs(false, 'f', vapp(VFin, false, m), f => vindfin([f].concat(rest2).concat([m]))))),
      true, v.cap), false, VFinLit(v.index - 1n, v.cap));
  }
  if (v.tag === 'VNe') {
    if (v.args.tag === 'Cons' && v.args.head.tag === 'EFS') {
      const rest2 = rest.slice(0, -1);
      // genindFin {P} z s {S k} (FS {k} x) ~> s (\{m : Nat} (f : Fin m). genindFin {P} z s {m} f) {k} x
      return vapp(vapp(vapp(rest[2], false, VAbs(true, 'm', VNat, m => VAbs(false, 'f', vapp(VFin, false, m), f => vindfin([f].concat(rest2).concat([m]))))), true, v.args.head.type), false, VNe(v.head, v.args.tail));
    }
    return VNe(v.head, Cons(EIndFin(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EIndFin(rest), v.args), mapLazy(v.val, v => vindfin([v].concat(rest))));
  return impossible(`vindnat: ${v.tag}`);
};
export const vifixind = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'IIn') {
      // genindIFix {I} {F} {P} f {i} (IIn {i} x) ~> f (\{i} y. genindIFix {I} {F} {P} f {i} y) {i} x 
      const [I, F, P, f, i] = rest;
      const args = v.args as Cons<Elim>;
      const x = (args.head as EApp).arg;
      return vapp(vapp(vapp(f, false,
        VAbs(true, 'i', I, i => VAbs(false, 'y', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), y => vifixind([y, I, F, P, f, i])))), true, i), false, x);
    }
    return VNe(v.head, Cons(EIFixInd(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EIFixInd(rest), v.args), mapLazy(v.val, v => vifixind([v].concat(rest))));
  return impossible(`vifixind: ${v.tag}`);
};

export const evaluate = (t: Term, vs: EnvV = Nil): Val => {
  if (t.tag === 'Prim') {
    if (t.name === 'elimHEq')
      return VAbs(true, 'A', VType, A =>
        VAbs(true, 'a', A, a =>
        VAbs(true, 'P', VPi(false, 'b', A, b => VPi(false, '_', vheq(A, A, a, b), _ => VType)), P =>
        VAbs(false, 'q', vapp(vapp(P, false, a), false, vapp(vapp(VPrim('ReflHEq'), true, A), true, a)), q =>
        VAbs(true, 'b', A, b =>
        VAbs(false, 'p', vheq(A, A, a, b), p =>
        velimheq([p, A, a, P, q, b])))))));
    if (t.name === 'unsafeElimHEq')
      return VAbs(true, 'A', VType, A =>
        VAbs(true, 'a', A, a =>
        VAbs(true, 'P', VPi(false, 'b', A, b => VPi(false, '_', vheq(A, A, a, b), _ => VType)), P =>
        VAbs(false, 'q', vapp(vapp(P, false, a), false, vapp(vapp(VPrim('ReflHEq'), true, A), true, a)), q =>
        VAbs(true, 'b', A, b =>
        VAbs(true, 'p', vheq(A, A, a, b), p =>
        velimheq([p, A, a, P, q, b])))))));
    if (t.name === 'S') return VAbs(false, 'n', VNat, n => vsucc(n));
    if (t.name === 'FS') return VAbs(true, 'n', VNat, n => VAbs(false, 'f', vapp(VFin, false, n), f => vfsucc(n, f)));
    if (t.name === 'genindNat')
      return VAbs(true, 'P', VPi(false, '_', VNat, _ => VType), P =>
        VAbs(false, 'z', vapp(P, false, VNatLit(0n)), z =>
        VAbs(false, 's', VPi(false, '_', VPi(false, 'k', VNat, k => vapp(P, false, k)), _ => VPi(false, 'm', VNat, m => vapp(P, false, vsucc(m)))), s =>
        VAbs(false, 'n', VNat, n =>
        vindnat([n, P, z, s])))));
    if (t.name === 'genindFin')
      return VAbs(true, 'P', VPi(false, 'i', VNat, i => VPi(false, '_', vapp(VFin, false, i), _ => VType)), P =>
        VAbs(false, 'z', VPi(true, 'n', VNat, n => vapp(vapp(P, false, vsucc(n)), false, VFinLit(0n, n))), z =>
        VAbs(false, 's',
          VPi(false, '_', VPi(true, 'i', VNat, i => VPi(false, 'x', vapp(VFin, false, i), x => vapp(vapp(P, false, i), false, x))), _ =>
          VPi(true, 'n', VNat, n =>
          VPi(false, 'y', vapp(VFin, false, n), y =>
          vapp(vapp(P, false, vsucc(n)), false, vfsucc(n, y))))), s =>
        VAbs(true, 'n', VNat, n =>
        VAbs(false, 'x', vapp(VFin, false, n), x =>
        vindfin([x, P, z, s, n]))))));
    if (t.name === 'genindIFix')
      return VAbs(true, 'I', VType, I =>
        VAbs(true, 'F', VPi(false, '_', VPi(false, '_', I, _ => VType), _ => VPi(false, '_', I, _ => VType)), F =>
        VAbs(true, 'P', VPi(false, 'i', I, i => VPi(false, '_', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), _ => VType)), P =>
        VAbs(false, 'f',
          VPi(false, '_', VPi(true, 'i', I, i => VPi(false, 'y', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), y => vapp(vapp(P, false, i), false, y))), _ =>
          VPi(true, 'i', I, i =>
          VPi(false, 'z', vapp(vapp(F, false, vapp(vapp(VIFix, false, I), false, F)), false, i), z =>
          vapp(vapp(P, false, i), false, vapp(vapp(vapp(vapp(VPrim('IIn'), true, I), true, F), true, i), false, z)))))
        , f =>
        VAbs(true, 'i', I, i =>
        VAbs(false, 'x', vapp(vapp(vapp(VIFix, false, I), false, F), false, i), x =>
        vifixind([x, I, F, P, f, i])))))));
    return VPrim(t.name);
  }
  if (t.tag === 'Sort') return VSort(t.sort);
  if (t.tag === 'Var') {
    const val = index(vs, t.index) || impossible(`evaluate: var ${t.index} has no value`);
    // TODO: return VGlued(HVar(length(vs) - t.index - 1), Nil, lazyOf(val));
    return val;
  }
  if (t.tag === 'Meta') {
    const s = metaGet(t.index);
    return s.tag === 'Solved' ? s.val : VMeta(t.index);
  }
  if (t.tag === 'Global') {
    const entry = globalGet(t.name) || impossible(`evaluate: global ${t.name} has no value`);
    return VGlued(HGlobal(t.name), Nil, lazyOf(entry.val));
  }
  if (t.tag === 'App')
    return vapp(evaluate(t.left, vs), t.plicity, evaluate(t.right, vs));
  if (t.tag === 'Abs')
    return VAbs(t.plicity, t.name, evaluate(t.type, vs), v => evaluate(t.body, extendV(vs, v)));
  if (t.tag === 'Let')
    return evaluate(t.body, extendV(vs, evaluate(t.val, vs)));
  if (t.tag === 'Pi')
    return VPi(t.plicity, t.name, evaluate(t.type, vs), v => evaluate(t.body, extendV(vs, v)));
  if (t.tag === 'Sigma')
    return VSigma(t.plicity, t.plicity2, t.name, evaluate(t.type, vs), v => evaluate(t.body, extendV(vs, v)));
  if (t.tag === 'Pair')
    return VPair(t.plicity, t.plicity2, evaluate(t.fst, vs), evaluate(t.snd, vs), evaluate(t.type, vs));
  if (t.tag === 'Proj') return vproj(t.proj, evaluate(t.term, vs));
  if (t.tag === 'NatLit') return VNatLit(t.val);
  if (t.tag === 'FinLit') return VFinLit(t.index, evaluate(t.cap, vs));
  return t;
};

const quoteHead = (h: Head, k: Ix): Term => {
  if (h.tag === 'HVar') return Var(k - (h.index + 1));
  if (h.tag === 'HGlobal') return Global(h.name);
  if (h.tag === 'HMeta') return Meta(h.index);
  if (h.tag === 'HPrim') return Prim(h.name);
  return h;
};
const quoteHeadGlued = (h: Head, k: Ix): Term | null => {
  if (h.tag === 'HGlobal') return Global(h.name);
  if (h.tag === 'HMeta') return Meta(h.index);
  return null;
};
const quoteElim = (t: Term, e: Elim, k: Ix, full: boolean): Term => {
  if (e.tag === 'EApp') return App(t, e.plicity, quote(e.arg, k, full));
  if (e.tag === 'EProj') return Proj(e.proj, t);
  if (e.tag === 'EElimHEq') {
    const [A, a, P, q, b] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(App(Prim('elimHEq'), true, A), true, a), true, P), false, q), true, b), false, t);
  }
  if (e.tag === 'EElimHEqUnsafe') {
    const [A, a, P, q, b] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(App(Prim('elimHEq'), true, A), true, a), true, P), false, q), true, b), true, t);
  }
  if (e.tag === 'ES') return App(Prim('S'), false, t);
  if (e.tag === 'EFS') return App(App(Prim('FS'), true, quote(e.type, k, full)), false, t);
  if (e.tag === 'EIndNat') {
    const args = e.args.map(x => quote(x, k, full));
    return App(App(App(App(Prim('genindNat'), true, args[0]), false, args[1]), false, args[2]), false, t);
  }
  if (e.tag === 'EIndFin') {
    const args = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(Prim('genindFin'), true, args[0]), false, args[1]), false, args[2]), true, args[3]), false, t);
  }
  if (e.tag === 'EIFixInd') {
    const [I, F, P, f, i] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(App(Prim('genindIFix'), true, I), true, F), true, P), false, f), true, i), false, t);
  }
  return e;
};
export const quote = (v_: Val, k: Ix, full: boolean): Term => {
  const v = forceGlue(v_);
  if (v.tag === 'VSort') return Sort(v.sort);
  if (v.tag === 'VNatLit') return NatLit(v.val);
  if (v.tag === 'VFinLit') return FinLit(v.index, quote(v.cap, k, full));
  if (v.tag === 'VNe')
    return foldr(
      (x, y) => quoteElim(y, x, k, full),
      quoteHead(v.head, k),
      v.args,
    );
  if (v.tag === 'VGlued') {
    if (full) return quote(forceLazy(v.val), k, full);
    const head = quoteHeadGlued(v.head, k);
    if (!head) return quote(forceLazy(v.val), k, full);
    return foldr(
      (x, y) => quoteElim(y, x, k, full),
      head,
      v.args,
    );
  }
  if (v.tag === 'VAbs')
    return Abs(v.plicity, v.name, quote(v.type, k, full), quote(v.body(VVar(k)), k + 1, full));
  if (v.tag === 'VPi')
    return Pi(v.plicity, v.name, quote(v.type, k, full), quote(v.body(VVar(k)), k + 1, full));
  if (v.tag === 'VSigma')
    return Sigma(v.plicity, v.plicity2, v.name, quote(v.type, k, full), quote(v.body(VVar(k)), k + 1, full));
  if (v.tag === 'VPair')
    return Pair(v.plicity, v.plicity2, quote(v.fst, k, full), quote(v.snd, k, full), quote(v.type, k, full));
  return v;
};
export const quoteZ = (v: Val, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): Term =>
  zonk(quote(v, k, full), vs, k, full);

export const normalize = (t: Term, vs: EnvV, k: Ix, full: boolean): Term =>
  quote(evaluate(t, vs), k, full);

export const showTermQ = (v: Val, k: number = 0, full: boolean = false): string => showTerm(quote(v, k, full));
export const showTermQZ = (v: Val, vs: EnvV = Nil, k: number = 0, full: boolean = false): string => showTerm(quoteZ(v, vs, k, full));
export const showTermS = (v: Val, ns: List<Name> = Nil, k: number = 0, full: boolean = false): string =>
  showSurface(quote(v, k, full), ns);
export const showTermSZ = (v: Val, ns: List<Name> = Nil, vs: EnvV = Nil, k: number = 0, full: boolean = false): string =>
  showSurface(quoteZ(v, vs, k, full), ns);
export const showElimQ = (e: Elim, k: number = 0, full: boolean = false): string => {
  if (e.tag === 'EApp') return `${e.plicity ? '{' : ''}${showTermQ(e.arg, k, full)}${e.plicity ? '}' : ''}`;
  return e.tag;
};
export const showElim = (e: Elim, ns: List<Name> = Nil, k: number = 0, full: boolean = false): string => {
  if (e.tag === 'EApp') return `${e.plicity ? '{' : ''}${showTermS(e.arg, ns, k, full)}${e.plicity ? '}' : ''}`;
  if (e.tag === 'EProj') return e.proj;
  if (e.tag === 'EElimHEq') return `elimheq ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'EElimHEqUnsafe') return `unsafeElimheq ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'ES') return 'succ';
  if (e.tag === 'EFS') return `fsucc {${showTermS(e.type, ns, k, full)}}`;
  if (e.tag === 'EIndNat') return `genindnat ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'EIndFin') return `genindfin ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'EIFixInd') return `genindifix ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  return e;
};

type S = [false, Val] | [true, Term];
const zonkSpine = (tm: Term, vs: EnvV, k: Ix, full: boolean): S => {
  if (tm.tag === 'Meta') {
    const s = metaGet(tm.index);
    if (s.tag === 'Unsolved') return [true, zonk(tm, vs, k, full)];
    return [false, s.val];
  }
  if (tm.tag === 'App') {
    const spine = zonkSpine(tm.left, vs, k, full);
    return spine[0] ?
      [true, App(spine[1], tm.plicity, zonk(tm.right, vs, k, full))] :
      [false, vapp(spine[1], tm.plicity, evaluate(tm.right, vs))];
  }
  // TODO: zonk other elims
  return [true, zonk(tm, vs, k, full)];
};
export const zonk = (tm: Term, vs: EnvV = Nil, k: Ix = 0, full: boolean = false): Term => {
  if (tm.tag === 'Meta') {
    const s = metaGet(tm.index);
    return s.tag === 'Solved' ? quote(s.val, k, full) : tm;
  }
  if (tm.tag === 'Pi')
    return Pi(tm.plicity, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Sigma')
    return Sigma(tm.plicity, tm.plicity2, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Let')
    return Let(tm.plicity, tm.name, zonk(tm.type, vs, k, full), zonk(tm.val, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Abs')
    return Abs(tm.plicity, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Pair')
    return Pair(tm.plicity, tm.plicity2, zonk(tm.fst, vs, k, full), zonk(tm.snd, vs, k, full), zonk(tm.type, vs, k, full));
  if (tm.tag === 'App') {
    const spine = zonkSpine(tm.left, vs, k, full);
    return spine[0] ?
      App(spine[1], tm.plicity, zonk(tm.right, vs, k, full)) :
      quote(vapp(spine[1], tm.plicity, evaluate(tm.right, vs)), k, full);
  }
  if (tm.tag === 'Proj') return Proj(tm.proj, zonk(tm.term, vs, k, full));
  if (tm.tag === 'FinLit')
    return FinLit(tm.index, zonk(tm.cap, vs, k, full));
  return tm;
};

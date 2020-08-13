import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr, toArray, length } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pi, Global, showSurface, Meta, Let, Sigma, Pair, Prim, Proj, Data, TCon, Con, DElim, Sort } from './syntax';
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

export type Elim = EApp | EProj | EElimHEq | EElim;

export type EApp = { tag: 'EApp', plicity: Plicity, arg: Val };
export const EApp = (plicity: Plicity, arg: Val): EApp => ({ tag: 'EApp', plicity, arg });
export type EProj = { tag: 'EProj', proj: 'fst' | 'snd' };
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });
export type EElimHEq = { tag: 'EElimHEq', args: Val[] };
export const EElimHEq = (args: Val[]): EElimHEq => ({ tag: 'EElimHEq', args });
export type EElim = { tag: 'EElim', args: Val[] };
export const EElim = (args: Val[]): EElim => ({ tag: 'EElim', args });

export type Clos = (val: Val) => Val;
export type Val = VNe | VGlued | VAbs | VPi | VSigma | VPair | VData | VTCon | VCon | VSort;

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
export type VData = { tag: 'VData', index: Val, cons: Val[] };
export const VData = (index: Val, cons: Val[]): VData => ({ tag: 'VData', index, cons });
export type VTCon = { tag: 'VTCon', data: Val, arg: Val };
export const VTCon = (data: Val, arg: Val): VTCon => ({ tag: 'VTCon', data, arg });
export type VCon = { tag: 'VCon', index: Ix, data: Val, arg: Val };
export const VCon = (index: Ix, data: Val, arg: Val): VCon => ({ tag: 'VCon', data, index, arg });
export type VSort = { tag: 'VSort', sort: Sorts };
export const VSort = (sort: Sorts): VSort => ({ tag: 'VSort', sort });

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);
export const VGlobal = (name: Name): VNe => VNe(HGlobal(name), Nil);
export const VMeta = (index: Ix): VNe => VNe(HMeta(index), Nil);
export const VPrim = (name: PrimName): VNe => VNe(HPrim(name), Nil);

export const VType = VSort('*');
export const VDesc = VSort('#');

export const VHEq = VPrim('HEq');
export const VReflHEq = VPrim('ReflHEq');
export const VUnitType = VPrim('UnitType');
export const VUnit = VPrim('Unit');
export const vheq = (A: Val, B: Val, a: Val, b: Val) => vapp(vapp(vapp(vapp(VHEq, true, A), true, B), false, a), false, b);

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
      elim.tag === 'EElim' ? velim([y].concat(elim.args)) :
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
      elim.tag === 'EElim' ? velim([y].concat(elim.args)) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};

export const isCanonical = (v: Val): boolean => {
  if (v.tag !== 'VNe') return true;
  if (v.head.tag === 'HGlobal') return true;
  if (v.head.tag === 'HPrim') return true;
  return false;
};
export const vapp = (a: Val, plicity: Plicity, b: Val): Val => {
  if (a.tag === 'VAbs') {
    if (a.plicity !== plicity) {
      return impossible(`plicity mismatch in vapp`);
    }
    return a.body(b);
  }
  if (a.tag === 'VNe') {
    // fix {a} {b} f @ x ~> f (fix {a} {b} f) x
    if (a.head.tag === 'HPrim' && a.head.name === 'drec' && length(a.args) === 3 && isCanonical(b)) {
      if (plicity) return impossible(`plicity mismatch in vapp: drec`);
      const [ta, tb, f] = toArray(a.args, x => (x as EApp).arg).reverse();
      return vapp(vapp(f, false, vapp(vapp(vapp(VPrim('drec'), true, ta), true, tb), false, f)), false, b);
    }
    if (a.head.tag === 'HPrim' && a.head.name === 'dreci' && length(a.args) === 3 && isCanonical(b)) {
      if (!plicity) return impossible(`plicity mismatch in vapp: dreci`);
      const [ta, tb, f] = toArray(a.args, x => (x as EApp).arg).reverse();
      return vapp(vapp(f, false, vapp(vapp(vapp(VPrim('drec'), true, ta), true, tb), false, f)), true, b);
    }
    return VNe(a.head, Cons(EApp(plicity, b), a.args));
  }
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
export const velim = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VCon') {
    // elim (con i a) c1...cn ~> ci a
    const dcase = args[v.index + 4];
    return vapp(dcase, false, v.arg);
  }
  if (v.tag === 'VNe')
    return VNe(v.head, Cons(EElim(rest), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EElim(rest), v.args), mapLazy(v.val, v => velim([v].concat(rest))));
  return impossible(`velim: ${v.tag}`);
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
  if (t.tag === 'Data') return VData(evaluate(t.index, vs), t.cons.map(x => evaluate(x, vs)));
  if (t.tag === 'TCon') return VTCon(evaluate(t.data, vs), evaluate(t.arg, vs));
  if (t.tag === 'Con') return VCon(t.index, evaluate(t.data, vs), evaluate(t.arg, vs));
  if (t.tag === 'DElim') {
    const args = [t.scrut, t.data, t.motive, t.index].concat(t.args).map(x => evaluate(x, vs));
    return velim(args);
  }
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
  if (e.tag === 'EElim') {
    const args = e.args.map(x => quote(x, k, full));
    return DElim(args[0], args[1], args[2], t, args.slice(3));
  }
  return e;
};
export const quote = (v_: Val, k: Ix, full: boolean): Term => {
  const v = forceGlue(v_);
  if (v.tag === 'VSort') return Sort(v.sort);
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
  if (v.tag === 'VData')
    return Data(quote(v.index, k, full), v.cons.map(x => quote(x, k, full)));
  if (v.tag === 'VTCon')
    return TCon(quote(v.data, k, full), quote(v.arg, k, full));
  if (v.tag === 'VCon')
    return Con(v.index, quote(v.data, k, full), quote(v.arg, k, full));
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
  if (e.tag === 'EElim') return `elim ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
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
  if (tm.tag === 'Data') return Data(zonk(tm.index, vs, k, full), tm.cons.map(x => zonk(x, vs, k, full)));
  if (tm.tag === 'TCon') return TCon(zonk(tm.data, vs, k, full), zonk(tm.arg, vs, k, full));
  if (tm.tag === 'Con') return Con(tm.index, zonk(tm.data, vs, k, full), zonk(tm.arg, vs, k, full));
  if (tm.tag === 'DElim')
    return DElim(zonk(tm.data, vs, k, full), zonk(tm.motive, vs, k, full), zonk(tm.index, vs, k, full), zonk(tm.scrut, vs, k, full), tm.args.map(x => zonk(x, vs, k, full)));
  return tm;
};

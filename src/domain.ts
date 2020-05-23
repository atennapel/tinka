import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pi, Global, showSurface, Meta, Let, Sort, UnsafeCast, Sigma, Pair, Fst, Snd, Enum, Elem } from './syntax';
import { impossible } from './utils/utils';
import { Lazy, mapLazy, forceLazy, lazyOf } from './utils/lazy';
import { Plicity, Sorts } from './surface';
import { globalGet } from './globalenv';
import { metaGet } from './metas';

export type Head = HVar | HGlobal | HMeta;

export type HVar = { tag: 'HVar', index: Ix };
export const HVar = (index: Ix): HVar => ({ tag: 'HVar', index });
export type HGlobal = { tag: 'HGlobal', name: Name };
export const HGlobal = (name: Name): HGlobal => ({ tag: 'HGlobal', name });
export type HMeta = { tag: 'HMeta', index: Ix };
export const HMeta = (index: Ix): HMeta => ({ tag: 'HMeta', index });

export type Elim = EApp | EUnsafeCast | EFst | ESnd;

export type EApp = { tag: 'EApp', plicity: Plicity, arg: Val };
export const EApp = (plicity: Plicity, arg: Val): EApp => ({ tag: 'EApp', plicity, arg });
export type EUnsafeCast = { tag: 'EUnsafeCast', type: Val };
export const EUnsafeCast = (type: Val): EUnsafeCast => ({ tag: 'EUnsafeCast', type });
export type EFst = { tag: 'EFst' };
export const EFst: EFst = { tag: 'EFst' };
export type ESnd = { tag: 'ESnd' };
export const ESnd: ESnd = { tag: 'ESnd' };

export type Clos = (val: Val) => Val;
export type Val = VNe | VGlued | VAbs | VPi | VSigma | VSort | VPair | VEnum | VElem;

export type VNe = { tag: 'VNe', head: Head, args: List<Elim> };
export const VNe = (head: Head, args: List<Elim>): VNe => ({ tag: 'VNe', head, args });
export type VGlued = { tag: 'VGlued', head: Head, args: List<Elim>, val: Lazy<Val> };
export const VGlued = (head: Head, args: List<Elim>, val: Lazy<Val>): VGlued => ({ tag: 'VGlued', head, args, val });
export type VAbs = { tag: 'VAbs', plicity: Plicity, name: Name, type: Val, body: Clos };
export const VAbs = (plicity: Plicity, name: Name, type: Val, body: Clos): VAbs => ({ tag: 'VAbs', plicity, name, type, body});
export type VPi = { tag: 'VPi', plicity: Plicity, name: Name, type: Val, body: Clos };
export const VPi = (plicity: Plicity, name: Name, type: Val, body: Clos): VPi => ({ tag: 'VPi', plicity, name, type, body});
export type VSigma = { tag: 'VSigma', name: Name, type: Val, body: Clos };
export const VSigma = (name: Name, type: Val, body: Clos): VSigma => ({ tag: 'VSigma', name, type, body});
export type VSort = { tag: 'VSort', sort: Sorts };
export const VSort = (sort: Sorts): VSort => ({ tag: 'VSort', sort });
export type VPair = { tag: 'VPair', fst: Val, snd: Val, type: Val };
export const VPair = (fst: Val, snd: Val, type: Val): VPair => ({ tag: 'VPair', fst, snd, type });
export type VEnum = { tag: 'VEnum', num: number };
export const VEnum = (num: number): VEnum => ({ tag: 'VEnum', num });
export type VElem = { tag: 'VElem', num: number, total: number };
export const VElem = (num: number, total: number): VElem => ({ tag: 'VElem', num, total });

export const VType: VSort = VSort('*');

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);
export const VGlobal = (name: Name): VNe => VNe(HGlobal(name), Nil);
export const VMeta = (index: Ix): VNe => VNe(HMeta(index), Nil);

export type EnvV = List<Val>;
export const extendV = (vs: EnvV, val: Val): EnvV => Cons(val, vs);
export const showEnvV = (l: EnvV, k: Ix = 0, full: boolean = false): string => listToString(l, v => showTerm(quote(v, k, full)));

export const force = (v: Val): Val => {
  if (v.tag === 'VGlued') return force(forceLazy(v.val));
  if (v.tag === 'VNe' && v.head.tag === 'HMeta') {
    const val = metaGet(v.head.index);
    if (val.tag === 'Unsolved') return v;
    return force(foldr((elim, y) =>
      elim.tag === 'EUnsafeCast' ? vunsafecast(elim.type, y) :
      elim.tag === 'EFst' ? vfst(y) :
      elim.tag === 'ESnd' ? vsnd(y) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};
export const forceGlue = (v: Val): Val => {
  if (v.tag === 'VNe' && v.head.tag === 'HMeta') {
    const val = metaGet(v.head.index);
    if (val.tag === 'Unsolved') return v;
    return forceGlue(foldr((elim, y) =>
      elim.tag === 'EUnsafeCast' ? vunsafecast(elim.type, y) :
      elim.tag === 'EFst' ? vfst(y) :
      elim.tag === 'ESnd' ? vsnd(y) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};

// do the eliminators have to force?
export const vapp = (a: Val, plicity: Plicity, b: Val): Val => {
  if (a.tag === 'VAbs') {
    if (a.plicity !== plicity) return impossible(`plicity mismatch in vapp`);
    return a.body(b);
  }
  if (a.tag === 'VNe') return VNe(a.head, Cons(EApp(plicity, b), a.args));
  if (a.tag === 'VGlued')
    return VGlued(a.head, Cons(EApp(plicity, b), a.args), mapLazy(a.val, v => vapp(v, plicity, b)));
  return impossible(`vapp: ${a.tag}`);
};
export const vunsafecast = (type: Val, v: Val): Val => {
  if (v.tag === 'VNe') return VNe(v.head, Cons(EUnsafeCast(type), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EUnsafeCast(type), v.args), mapLazy(v.val, v => vunsafecast(type, v)));
  return v;
};
export const vfst = (v: Val): Val => {
  if (v.tag === 'VPair') return v.fst;
  if (v.tag === 'VNe') return VNe(v.head, Cons(EFst, v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EFst, v.args), mapLazy(v.val, v => vfst(v)));
  return impossible(`vfst: ${v.tag}`);
};
export const vsnd = (v: Val): Val => {
  if (v.tag === 'VPair') return v.snd;
  if (v.tag === 'VNe') return VNe(v.head, Cons(ESnd, v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(ESnd, v.args), mapLazy(v.val, v => vsnd(v)));
  return impossible(`vsnd: ${v.tag}`);
};

export const evaluate = (t: Term, vs: EnvV = Nil): Val => {
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
    return VSigma(t.name, evaluate(t.type, vs), v => evaluate(t.body, extendV(vs, v)));
  if (t.tag === 'UnsafeCast')
    return vunsafecast(evaluate(t.type, vs), evaluate(t.val, vs));
  if (t.tag === 'Pair')
    return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs), evaluate(t.type, vs));
  if (t.tag === 'Fst') return vfst(evaluate(t.term, vs));
  if (t.tag === 'Snd') return vsnd(evaluate(t.term, vs));
  if (t.tag === 'Enum') return VEnum(t.num);
  if (t.tag === 'Elem') return VElem(t.num, t.total);
  return t;
};

const quoteHead = (h: Head, k: Ix): Term => {
  if (h.tag === 'HVar') return Var(k - (h.index + 1));
  if (h.tag === 'HGlobal') return Global(h.name);
  if (h.tag === 'HMeta') return Meta(h.index);
  return h;
};
const quoteHeadGlued = (h: Head, k: Ix): Term | null => {
  if (h.tag === 'HGlobal') return Global(h.name);
  if (h.tag === 'HMeta') return Meta(h.index);
  return null;
};
const quoteElim = (t: Term, e: Elim, k: Ix, full: boolean): Term => {
  if (e.tag === 'EApp') return App(t, e.plicity, quote(e.arg, k, full));
  if (e.tag === 'EUnsafeCast') return UnsafeCast(quote(e.type, k, full), t);
  if (e.tag === 'EFst') return Fst(t);
  if (e.tag === 'ESnd') return Snd(t);
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
    return Sigma(v.name, quote(v.type, k, full), quote(v.body(VVar(k)), k + 1, full));
  if (v.tag === 'VPair')
    return Pair(quote(v.fst, k, full), quote(v.snd, k, full), quote(v.type, k, full));
  if (v.tag === 'VEnum') return Enum(v.num);
  if (v.tag === 'VElem') return Elem(v.num, v.total);
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
  if (e.tag === 'EUnsafeCast') return `unsafeCast {${showTermS(e.type, ns, k, full)}}`;
  if (e.tag === 'EFst') return `fst`;
  if (e.tag === 'ESnd') return `snd`;
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
    return Sigma(tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Let')
    return Let(tm.plicity, tm.name, zonk(tm.type, vs, k, full), zonk(tm.val, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Abs')
    return Abs(tm.plicity, tm.name, zonk(tm.type, vs, k, full), zonk(tm.body, extendV(vs, VVar(k)), k + 1, full));
  if (tm.tag === 'Pair')
    return Pair(zonk(tm.fst, vs, k, full), zonk(tm.snd, vs, k, full), zonk(tm.type, vs, k, full));
  if (tm.tag === 'App') {
    const spine = zonkSpine(tm.left, vs, k, full);
    return spine[0] ?
      App(spine[1], tm.plicity, zonk(tm.right, vs, k, full)) :
      quote(vapp(spine[1], tm.plicity, evaluate(tm.right, vs)), k, full);
  }
  if (tm.tag === 'UnsafeCast') return UnsafeCast(zonk(tm.type, vs, k, full), zonk(tm.val, vs, k, full));
  if (tm.tag === 'Fst') return Fst(zonk(tm.term, vs, k, full));
  if (tm.tag === 'Snd') return Snd(zonk(tm.term, vs, k, full));
  return tm;
};

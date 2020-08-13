import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pi, Global, showSurface, Meta, Let, Sigma, Pair, Prim, Proj, Type, Data, TCon, Con } from './syntax';
import { impossible } from './utils/utils';
import { Lazy, mapLazy, forceLazy, lazyOf } from './utils/lazy';
import { Plicity, PrimName } from './surface';
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

export type Elim = EApp | EProj | EIFixInd | EElimHEq | EIndBool;

export type EApp = { tag: 'EApp', plicity: Plicity, arg: Val };
export const EApp = (plicity: Plicity, arg: Val): EApp => ({ tag: 'EApp', plicity, arg });
export type EProj = { tag: 'EProj', proj: 'fst' | 'snd' };
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });
export type EIFixInd = { tag: 'EIFixInd', args: Val[] };
export const EIFixInd = (args: Val[]): EIFixInd => ({ tag: 'EIFixInd', args });
export type EElimHEq = { tag: 'EElimHEq', args: Val[] };
export const EElimHEq = (args: Val[]): EElimHEq => ({ tag: 'EElimHEq', args });
export type EIndBool = { tag: 'EIndBool', args: Val[] };
export const EIndBool = (args: Val[]): EIndBool => ({ tag: 'EIndBool', args });

export type Clos = (val: Val) => Val;
export type Val = VNe | VGlued | VAbs | VPi | VSigma | VPair | VData | VTCon | VCon | VType;

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
export type VType = { tag: 'VType' };
export const VType: VType = { tag: 'VType' };

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);
export const VGlobal = (name: Name): VNe => VNe(HGlobal(name), Nil);
export const VMeta = (index: Ix): VNe => VNe(HMeta(index), Nil);
export const VPrim = (name: PrimName): VNe => VNe(HPrim(name), Nil);

export const VDesc = VPrim('Desc');
export const VIFix = VPrim('IFix');
export const VHEq = VPrim('HEq');
export const VReflHEq = VPrim('ReflHEq');
export const VUnitType = VPrim('UnitType');
export const VUnit = VPrim('Unit');
export const VBool = VPrim('Bool');
export const VTrue = VPrim('True');
export const VFalse = VPrim('False');
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
      elim.tag === 'EIFixInd' ? vifixind([y].concat(elim.args)) :
      elim.tag === 'EElimHEq' ? velimheq([y].concat(elim.args)) :
      elim.tag === 'EIndBool' ? vindbool([y].concat(elim.args)) :
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
      elim.tag === 'EIFixInd' ? vifixind([y].concat(elim.args)) :
      elim.tag === 'EElimHEq' ? velimheq([y].concat(elim.args)) :
      elim.tag === 'EIndBool' ? vindbool([y].concat(elim.args)) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};

// do the eliminators have to force?
export const vapp = (a: Val, plicity: Plicity, b: Val): Val => {
  if (a.tag === 'VAbs') {
    if (a.plicity !== plicity) {
      console.log(a, plicity, b);
      return impossible(`plicity mismatch in vapp`);
    }
    return a.body(b);
  }
  if (a.tag === 'VNe') return VNe(a.head, Cons(EApp(plicity, b), a.args));
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
export const vindbool = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'True') {
      // indBool {P} t f True ~> t
      return rest[1];
    }
    if (v.head.tag === 'HPrim' && v.head.name === 'False') {
      // indBool {P} t f False ~> f
      return rest[2];
    }
    return VNe(v.head, Cons(EIndBool(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EIndBool(rest), v.args), mapLazy(v.val, v => vindbool([v].concat(rest))));
  return impossible(`vindbool: ${v.tag}`);
};

export const evaluate = (t: Term, vs: EnvV = Nil): Val => {
  if (t.tag === 'Prim') {
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
    if (t.name === 'elimHEq')
      return VAbs(true, 'A', VType, A =>
        VAbs(true, 'a', A, a =>
        VAbs(true, 'P', VPi(false, 'b', A, b => VPi(false, '_', vheq(A, A, a, b), _ => VType)), P =>
        VAbs(false, 'q', vapp(vapp(P, false, a), false, vapp(vapp(VPrim('ReflHEq'), true, A), true, a)), q =>
        VAbs(true, 'b', A, b =>
        VAbs(false, 'p', vheq(A, A, a, b), p =>
        velimheq([p, A, a, P, q, b])))))));
    if (t.name === 'indBool')
      return VAbs(true, 'P', VPi(false, '_', VBool, _ => VType), P => VAbs(false, 't', vapp(P, false, VTrue), t => VAbs(false, 'f', vapp(P, false, VFalse), f => VAbs(false, 'x', VBool, x => vindbool([x, P, t, f])))));
    return VPrim(t.name);
  }
  if (t.tag === 'Type') return VType;
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
  if (e.tag === 'EIFixInd') {
    const [I, F, P, f, i] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(App(Prim('genindIFix'), true, I), true, F), true, P), false, f), true, i), false, t);
  }
  if (e.tag === 'EElimHEq') {
    const [A, a, P, q, b] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(App(Prim('elimHEq'), true, A), true, a), true, P), false, q), true, b), false, t);
  }
  if (e.tag === 'EIndBool') {
    const [P, pt, pf] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(Prim('indBool'), true, P), false, pt), false, pf), false, t);
  }
  return e;
};
export const quote = (v_: Val, k: Ix, full: boolean): Term => {
  const v = forceGlue(v_);
  if (v.tag === 'VType') return Type;
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
  if (e.tag === 'EIFixInd') return `genindifix ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'EElimHEq') return `elimheq ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'EIndBool') return `indbool ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
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
  return tm;
};

import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr, toArray } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pi, Global, showSurface, Meta, Let, Sigma, Pair, Enum, Elem, EnumInd, Prim, Proj } from './syntax';
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

export type Elim = EApp | EUnsafeCast | EProj | EEnumInd | EDescInd | EFixInd;

export type EApp = { tag: 'EApp', plicity: Plicity, arg: Val };
export const EApp = (plicity: Plicity, arg: Val): EApp => ({ tag: 'EApp', plicity, arg });
export type EUnsafeCast = { tag: 'EUnsafeCast', type: Val, fromtype: Val };
export const EUnsafeCast = (type: Val, fromtype: Val): EUnsafeCast => ({ tag: 'EUnsafeCast', type, fromtype });
export type EProj = { tag: 'EProj', proj: 'fst' | 'snd' };
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });
export type EEnumInd = { tag: 'EEnumInd', num: number, prop: Val, args: Val[] };
export const EEnumInd = (num: number, prop: Val, args: Val[]): EEnumInd => ({ tag: 'EEnumInd', num, prop, args });
export type EDescInd = { tag: 'EDescInd', args: Val[] };
export const EDescInd = (args: Val[]): EDescInd => ({ tag: 'EDescInd', args });
export type EFixInd = { tag: 'EFixInd', args: Val[] };
export const EFixInd = (args: Val[]): EFixInd => ({ tag: 'EFixInd', args });

export type Clos = (val: Val) => Val;
export type Val = VNe | VGlued | VAbs | VPi | VSigma | VPair | VEnum | VElem;

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
export type VPair = { tag: 'VPair', fst: Val, snd: Val, type: Val };
export const VPair = (fst: Val, snd: Val, type: Val): VPair => ({ tag: 'VPair', fst, snd, type });
export type VEnum = { tag: 'VEnum', num: number };
export const VEnum = (num: number): VEnum => ({ tag: 'VEnum', num });
export type VElem = { tag: 'VElem', num: number, total: number };
export const VElem = (num: number, total: number): VElem => ({ tag: 'VElem', num, total });

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);
export const VGlobal = (name: Name): VNe => VNe(HGlobal(name), Nil);
export const VMeta = (index: Ix): VNe => VNe(HMeta(index), Nil);
export const VPrim = (name: PrimName): VNe => VNe(HPrim(name), Nil);

export const VType = VPrim('*');
export const VDesc = VPrim('Desc');
export const VFix = VPrim('Fix');

export type EnvV = List<Val>;
export const extendV = (vs: EnvV, val: Val): EnvV => Cons(val, vs);
export const showEnvV = (l: EnvV, k: Ix = 0, full: boolean = false): string => listToString(l, v => showTerm(quote(v, k, full)));

export const force = (v: Val): Val => {
  if (v.tag === 'VGlued') return force(forceLazy(v.val));
  if (v.tag === 'VNe' && v.head.tag === 'HMeta') {
    const val = metaGet(v.head.index);
    if (val.tag === 'Unsolved') return v;
    return force(foldr((elim, y) =>
      elim.tag === 'EUnsafeCast' ? vunsafecast(elim.type, elim.fromtype, y) :
      elim.tag === 'EProj' ? vproj(elim.proj, y) :
      elim.tag === 'EEnumInd' ? venumind(elim.num, elim.prop, elim.args, y) :
      elim.tag === 'EDescInd' ? vdescind([y].concat(elim.args)) :
      elim.tag === 'EFixInd' ? vfixind([y].concat(elim.args)) :
      vapp(y, elim.plicity, elim.arg), val.val, v.args));
  }
  return v;
};
export const forceGlue = (v: Val): Val => {
  if (v.tag === 'VNe' && v.head.tag === 'HMeta') {
    const val = metaGet(v.head.index);
    if (val.tag === 'Unsolved') return v;
    return forceGlue(foldr((elim, y) =>
      elim.tag === 'EUnsafeCast' ? vunsafecast(elim.type, elim.fromtype, y) :
      elim.tag === 'EProj' ? vproj(elim.proj, y) :
      elim.tag === 'EEnumInd' ? venumind(elim.num, elim.prop, elim.args, y) :
      elim.tag === 'EDescInd' ? vdescind([y].concat(elim.args)) :
      elim.tag === 'EFixInd' ? vfixind([y].concat(elim.args)) :
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
export const vunsafecast = (type: Val, fromtype: Val, v: Val): Val => {
  if (v.tag === 'VNe') return VNe(v.head, Cons(EUnsafeCast(type, fromtype), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EUnsafeCast(type, fromtype), v.args), mapLazy(v.val, v => vunsafecast(type, fromtype, v)));
  return v;
};
export const vproj = (proj: 'fst' | 'snd', v: Val): Val => {
  if (v.tag === 'VPair') return proj === 'fst' ? v.fst : v.snd;
  if (v.tag === 'VNe') return VNe(v.head, Cons(EProj(proj), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EProj(proj), v.args), mapLazy(v.val, v => vproj(proj, v)));
  return impossible(`vsnd: ${v.tag}`);
};
export const venumind = (n: number, prop: Val, args: Val[], v: Val): Val => {
  if (v.tag === 'VElem') return args[v.num];
  if (v.tag === 'VNe') return VNe(v.head, Cons(EEnumInd(n, prop, args), v.args));
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EEnumInd(n, prop, args), v.args), mapLazy(v.val, v => venumind(n, prop, args, v)));
  return impossible(`venumind: ${v.tag}`);
};
export const vdescind = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim') {
      if (v.head.name === 'End') return args[2];
      if (v.head.name === 'Rec') {
        const arg = ((v.args as Cons<Elim>).head as EApp).arg;
        return vapp(vapp(args[3], false, arg), false, vdescind([arg].concat(rest)));
      }
      if (v.head.name === 'Arg') {
        const as = toArray(v.args, e => (e as EApp).arg).reverse();
        return vapp(vapp(vapp(args[4], true, as[0]), false, as[1]), false, VAbs(false, 'x', as[0], x => vdescind([vapp(as[1], false, x)].concat(rest))));
      }
    }
    return VNe(v.head, Cons(EDescInd(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EDescInd(rest), v.args), mapLazy(v.val, v => vdescind([v].concat(rest))));
  return impossible(`vdescind: ${v.tag}`);
};
export const vfixind = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'In') {
      const [D, P, f] = rest;
      const d = ((v.args as Cons<Elim>).head as EApp).arg;
      return vapp(
        vapp(f, false, d), false,
        vapp(vapp(vapp(vapp(vapp(evaluate(Global('allDesc')), false, D), true, vapp(VFix, false, D)), true, P), false, VAbs(false, 'x', vapp(VFix, false, D), x => vfixind([x, D, P, f]))), false, d)
      );
    }
    return VNe(v.head, Cons(EFixInd(rest), v.args));
  }
  if (v.tag === 'VGlued')
    return VGlued(v.head, Cons(EFixInd(rest), v.args), mapLazy(v.val, v => vfixind([v].concat(rest))));
  return impossible(`vfixind: ${v.tag}`);
};


export const evaluate = (t: Term, vs: EnvV = Nil): Val => {
  if (t.tag === 'Prim') {
    if (t.name === 'indFix')
      return VAbs(false, 'D', VDesc, D =>
        VAbs(false, 'x', vapp(VFix, false, D), x =>
        VAbs(true, 'P', VPi(false, '_', vapp(VFix, false, D), _ => VType), P =>
        VAbs(false, 'f', VPi(false, 'd', vapp(vapp(evaluate(Global('interpDesc')), false, D), false, vapp(VFix, false, D)), d => VPi(false, '_', vapp(vapp(vapp(vapp(evaluate(Global('AllDesc')), false, D), false, vapp(VFix, false, D)), false, P), false, d), _ => vapp(P, false, vapp(vapp(VPrim('In'), true, D), false, d)))), f =>
        vfixind([x, D, P, f])))));
    if (t.name === 'indDesc')
      return VAbs(false, 'x', VDesc, x =>
        VAbs(true, 'P', VPi(false, '_', VDesc, _ => VType), P =>
        VAbs(false, 'e', vapp(P, false, VPrim('End')), e =>
        VAbs(false, 'r', VPi(false, 'r', VDesc, r => VPi(false, '_', vapp(P, false, r), _ => vapp(P, false, vapp(VPrim('Rec'), false, r)))), r =>
        VAbs(false, 'a', VPi(true, 't', VType, t => VPi(false, 'f', VPi(false, '_', t, _ => VDesc), f => VPi(false, '_', VPi(false, 'x', t, x => vapp(P, false, vapp(f, false, x))), _ => vapp(P, false, vapp(vapp(VPrim('Arg'), true, t), false, f))))), a =>
        vdescind([x, P, e, r, a]))))));
    if (t.name === 'unsafeCast')
      return VAbs(true, 'a', VType, a => VAbs(true, 'b', VType, b => VAbs(false, '_', b, x => vunsafecast(a, b, x))));
    return VPrim(t.name);
  }
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
  if (t.tag === 'Pair')
    return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs), evaluate(t.type, vs));
  if (t.tag === 'Proj') return vproj(t.proj, evaluate(t.term, vs));
  if (t.tag === 'Enum') return VEnum(t.num);
  if (t.tag === 'Elem') return VElem(t.num, t.total);
  if (t.tag === 'EnumInd')
    return venumind(t.num, evaluate(t.prop, vs), t.args.map(x => evaluate(x, vs)), evaluate(t.term, vs));
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
  if (e.tag === 'EEnumInd') return EnumInd(e.num, quote(e.prop, k, full), t, e.args.map(x => quote(x, k, full)));
  if (e.tag === 'EDescInd') {
    const [Pq, eq, rq, aq] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(App(Prim('indDesc'), false, t), true, Pq), false, eq), false, rq), false, aq);
  }
  if (e.tag === 'EFixInd') {
    const [D, P, f] = e.args.map(x => quote(x, k, full));
    return App(App(App(App(Prim('indFix'), false, D), false, t), true, P), false, f);
  }
  if (e.tag === 'EUnsafeCast') {
    const [type, fromtype] = [e.type, e.fromtype].map(x => quote(x, k, full));
    return App(App(App(Prim('unsafeCast'), true, type), true, fromtype), false, t);
  }
  return e;
};
export const quote = (v_: Val, k: Ix, full: boolean): Term => {
  const v = forceGlue(v_);
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
  if (e.tag === 'EProj') return e.proj;
  if (e.tag === 'EEnumInd') return `?${e.num} {${showTermS(e.prop, ns, k, full)}} ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`;
  if (e.tag === 'EDescInd') return `inddesc ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`
  if (e.tag === 'EFixInd') return `indfix ${e.args.map(x => showTermS(x, ns, k, full)).join(' ')}`
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
  if (tm.tag === 'Proj') return Proj(tm.proj, zonk(tm.term, vs, k, full));
  if (tm.tag === 'EnumInd')
    return EnumInd(tm.num, zonk(tm.prop, vs, k, full), zonk(tm.term, vs, k, full), tm.args.map(x => zonk(x, vs, k, full)));
  return tm;
};

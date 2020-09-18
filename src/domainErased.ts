import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pair, Prim, Proj, NatLit, Type, PrimName } from './erased';
import { impossible } from './utils/utils';
import { globalGet } from './globalenv';

export type Head = HVar | HPrim;

export type HVar = { tag: 'HVar', index: Ix };
export const HVar = (index: Ix): HVar => ({ tag: 'HVar', index });
export type HPrim = { tag: 'HPrim', name: PrimName };
export const HPrim = (name: PrimName): HPrim => ({ tag: 'HPrim', name });

export type Elim = EApp | EProj | EElimHEq | ES | EIndNat | EIFixInd;

export type EApp = { tag: 'EApp', arg: Val };
export const EApp = (arg: Val): EApp => ({ tag: 'EApp', arg });
export type EProj = { tag: 'EProj', proj: 'fst' | 'snd' };
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });
export type EElimHEq = { tag: 'EElimHEq', arg: Val };
export const EElimHEq = (arg: Val): EElimHEq => ({ tag: 'EElimHEq', arg });
export type ES = { tag: 'ES' };
export const ES: ES = { tag: 'ES' };
export type EIndNat = { tag: 'EIndNat', args: Val[] };
export const EIndNat = (args: Val[]): EIndNat => ({ tag: 'EIndNat', args });
export type EIFixInd = { tag: 'EIFixInd', arg: Val };
export const EIFixInd = (arg: Val): EIFixInd => ({ tag: 'EIFixInd', arg });

export type Clos = (val: Val) => Val;
export type Val = VNe | VAbs | VPair | VNatLit | VType;

export type VNe = { tag: 'VNe', head: Head, args: List<Elim> };
export const VNe = (head: Head, args: List<Elim>): VNe => ({ tag: 'VNe', head, args });
export type VAbs = { tag: 'VAbs', name: Name, body: Clos };
export const VAbs = (name: Name, body: Clos): VAbs => ({ tag: 'VAbs', name, body});
export type VPair = { tag: 'VPair', fst: Val, snd: Val };
export const VPair = (fst: Val, snd: Val): VPair => ({ tag: 'VPair', fst, snd });
export type VNatLit = { tag: 'VNatLit', val: bigint };
export const VNatLit = (val: bigint): VNatLit => ({ tag: 'VNatLit', val });
export type VType = { tag: 'VType' };
export const VType: VType = { tag: 'VType' };

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);
export const VPrim = (name: PrimName): VNe => VNe(HPrim(name), Nil);

export type EnvV = List<Val>;
export const extendV = (vs: EnvV, val: Val): EnvV => Cons(val, vs);
export const showEnvV = (l: EnvV, k: Ix = 0): string => listToString(l, v => showTerm(quote(v, k)));

export const vapp = (a: Val, b: Val): Val => {
  if (a.tag === 'VAbs') {
    return a.body(b);
  }
  if (a.tag === 'VNe')
    return VNe(a.head, Cons(EApp(b), a.args));
  return impossible(`vapp: ${a.tag}`);
};
export const vproj = (proj: 'fst' | 'snd', v: Val): Val => {
  if (v.tag === 'VPair') return proj === 'fst' ? v.fst : v.snd;
  if (v.tag === 'VNe') return VNe(v.head, Cons(EProj(proj), v.args));
  return impossible(`vsnd: ${v.tag}`);
};
export const velimheq = (v: Val, w: Val): Val => {
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'ReflHEq') {
      // elimHEq {A} {a} {P} q {b} (ReflHEq {A} {a}) ~> q 
      return w;
    }
    return VNe(v.head, Cons(EElimHEq(w), v.args));
  }
  return impossible(`velimheq: ${v.tag}`);
};
export const vsucc = (v: Val): Val => {
  if (v.tag === 'VNatLit') return VNatLit(v.val + 1n);
  if (v.tag === 'VNe')
    return VNe(v.head, Cons(ES, v.args));
  return impossible(`vsucc: ${v.tag}`);
};
export const vindnat = (args: Val[]): Val => {
  const v = args[0];
  const rest = args.slice(1);
  if (v.tag === 'VNatLit') {
    if (v.val === 0n) return rest[0];
    return vapp(vapp(rest[1], VAbs('k', k => vindnat([k].concat(rest)))), VNatLit(v.val - 1n));
  }
  if (v.tag === 'VNe') {
    if (v.args.tag === 'Cons' && v.args.head.tag === 'ES')
      return vapp(vapp(rest[1], VAbs('k', k => vindnat([k].concat(rest)))), VNe(v.head, v.args.tail));
    return VNe(v.head, Cons(EIndNat(rest), v.args));
  }
  return impossible(`vindnat: ${v.tag}`);
};
export const vifixind = (v: Val, f: Val): Val => {
  if (v.tag === 'VNe') {
    if (v.head.tag === 'HPrim' && v.head.name === 'IIn') {
      // genindIFix {I} {F} {P} f {i} (IIn {i} x) ~> f (\{i} y. genindIFix {I} {F} {P} f {i} y) {i} x 
      const args = v.args as Cons<Elim>;
      const x = (args.head as EApp).arg;
      return vapp(vapp(f, VAbs('y', y => vifixind(y, f))), x);
    }
    return VNe(v.head, Cons(EIFixInd(f), v.args));
  }
  return impossible(`vifixind: ${v.tag}`);
};

export const evaluate = (t: Term, vs: EnvV = Nil): Val => {
  if (t.tag === 'Prim') {
    if (t.name === 'elimHEq')
      return VAbs('q', q => VAbs('p', p => velimheq(p, q)));
    if (t.name === 'S') return VAbs('n', n => vsucc(n));
    if (t.name === 'genindNat')
      return VAbs('z', z => VAbs('s', s => VAbs('n', n => vindnat([n, z, s]))));
    if (t.name === 'genindIFix')
      return VAbs('f', f => VAbs('x', x => vifixind(x, f)));
    return VPrim(t.name);
  }
  if (t.tag === 'Var') {
    const val = index(vs, t.index) || impossible(`evaluate: var ${t.index} has no value`);
    // TODO: return VGlued(HVar(length(vs) - t.index - 1), Nil, lazyOf(val));
    return val;
  }
  if (t.tag === 'Global') {
    const entry = globalGet(t.name) || impossible(`evaluate: global ${t.name} has no value`);
    return evaluate(entry.erased); // TODO: store in global entry
  }
  if (t.tag === 'App')
    return vapp(evaluate(t.left, vs), evaluate(t.right, vs));
  if (t.tag === 'Abs')
    return VAbs(t.name, v => evaluate(t.body, extendV(vs, v)));
  if (t.tag === 'Let')
    return evaluate(t.body, extendV(vs, evaluate(t.val, vs)));
  if (t.tag === 'Pair')
    return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs));
  if (t.tag === 'Proj') return vproj(t.proj, evaluate(t.term, vs));
  if (t.tag === 'NatLit') return VNatLit(t.val);
  if (t.tag === 'Type') return VType;
  return t;
};

const quoteHead = (h: Head, k: Ix): Term => {
  if (h.tag === 'HVar') return Var(k - (h.index + 1));
  if (h.tag === 'HPrim') return Prim(h.name);
  return h;
};
const quoteElim = (t: Term, e: Elim, k: Ix): Term => {
  if (e.tag === 'EApp') return App(t, quote(e.arg, k));
  if (e.tag === 'EProj') return Proj(e.proj, t);
  if (e.tag === 'EElimHEq') {
    const q = quote(e.arg, k);
    return App(App(Prim('elimHEq'), q), t);
  }
  if (e.tag === 'ES') return App(Prim('S'), t);
  if (e.tag === 'EIndNat') {
    const [z, s] = e.args.map(x => quote(x, k));
    return App(App(App(Prim('genindNat'), z), s), t);
  }
  if (e.tag === 'EIFixInd') {
    const f = quote(e.arg, k);
    return App(App(Prim('genindIFix'), f), t);
  }
  return e;
};
export const quote = (v: Val, k: Ix): Term => {
  if (v.tag === 'VType') return Type;
  if (v.tag === 'VNatLit') return NatLit(v.val);
  if (v.tag === 'VNe')
    return foldr(
      (x, y) => quoteElim(y, x, k),
      quoteHead(v.head, k),
      v.args,
    );
  if (v.tag === 'VAbs')
    return Abs(v.name, quote(v.body(VVar(k)), k + 1));
  if (v.tag === 'VPair')
    return Pair(quote(v.fst, k), quote(v.snd, k));
  return v;
};

export const normalize = (t: Term, vs: EnvV = Nil, k: Ix = 0): Term => quote(evaluate(t, vs), k);

export const showTermQ = (v: Val, k: number = 0): string => showTerm(quote(v, k));
export const showTermS = (v: Val, ns: List<Name> = Nil, k: number = 0): string => showTerm(quote(v, k), ns);
export const showElimQ = (e: Elim, k: number = 0): string => {
  if (e.tag === 'EApp') return `${showTermQ(e.arg, k)}`;
  return e.tag;
};
export const showElim = (e: Elim, ns: List<Name> = Nil, k: number = 0): string => {
  if (e.tag === 'EApp') return `${showTermS(e.arg, ns, k)}`;
  if (e.tag === 'EProj') return e.proj;
  if (e.tag === 'EElimHEq') return `elimheq ${showTermS(e.arg, ns, k)}`;
  if (e.tag === 'ES') return 'succ';
  if (e.tag === 'EIndNat') return `genindnat ${e.args.map(x => showTermS(x, ns, k)).join(' ')}`;
  if (e.tag === 'EIFixInd') return `genindifix ${showTermS(e.arg, ns, k)}`;
  return e;
};
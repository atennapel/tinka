import { Ix, Name } from './names';
import { List, Cons, Nil, listToString, index, foldr } from './utils/list';
import { Term, showTerm, Var, App, Abs, Pair, Proj } from './erased';
import { impossible } from './utils/utils';
import { globalGet } from './globalenv';

export type Head = HVar;

export type HVar = { tag: 'HVar', index: Ix };
export const HVar = (index: Ix): HVar => ({ tag: 'HVar', index });

export type Elim = EApp | EProj;

export type EApp = { tag: 'EApp', arg: Val };
export const EApp = (arg: Val): EApp => ({ tag: 'EApp', arg });
export type EProj = { tag: 'EProj', proj: 'fst' | 'snd' };
export const EProj = (proj: 'fst' | 'snd'): EProj => ({ tag: 'EProj', proj });

export type Clos = (val: Val) => Val;
export type Val = VNe | VAbs | VPair;

export type VNe = { tag: 'VNe', head: Head, args: List<Elim> };
export const VNe = (head: Head, args: List<Elim>): VNe => ({ tag: 'VNe', head, args });
export type VAbs = { tag: 'VAbs', name: Name, body: Clos };
export const VAbs = (name: Name, body: Clos): VAbs => ({ tag: 'VAbs', name, body});
export type VPair = { tag: 'VPair', fst: Val, snd: Val };
export const VPair = (fst: Val, snd: Val): VPair => ({ tag: 'VPair', fst, snd });

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);

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

export const evaluate = (t: Term, vs: EnvV = Nil): Val => {
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
  return t;
};

const quoteHead = (h: Head, k: Ix): Term => {
  if (h.tag === 'HVar') return Var(k - (h.index + 1));
  return h.tag;
};
const quoteElim = (t: Term, e: Elim, k: Ix): Term => {
  if (e.tag === 'EApp') return App(t, quote(e.arg, k));
  if (e.tag === 'EProj') return Proj(e.proj, t);
  return e;
};
export const quote = (v: Val, k: Ix): Term => {
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
  return e;
};

import { Ix } from '../names';
import { List, Cons, Nil, listToString, index, foldr } from '../utils/list';
import { Term, showTerm, Var, App, Abs, Num, Inc, Pair } from './syntax';
import { impossible } from '../utils/util';

export type Head = HVar;

export type HVar = { tag: 'HVar', index: Ix };
export const HVar = (index: Ix): HVar => ({ tag: 'HVar', index });

export type Elim = EApp | EInc;

export type EApp = { tag: 'EApp', arg: Val };
export const EApp = (arg: Val): EApp => ({ tag: 'EApp', arg });
export type EInc = { tag: 'EInc' };
export const EInc: EInc = { tag: 'EInc' };

export type Clos = (val: Val) => Val;
export type Val = VNe | VAbs | VNum | VPair;

export type VNe = { tag: 'VNe', head: Head, args: List<Elim> };
export const VNe = (head: Head, args: List<Elim>): VNe => ({ tag: 'VNe', head, args });
export type VAbs = { tag: 'VAbs', body: Clos };
export const VAbs = (body: Clos): VAbs => ({ tag: 'VAbs', body });
export type VNum = { tag: 'VNum', value: number };
export const VNum = (value: number): VNum => ({ tag: 'VNum', value });
export type VPair = { tag: 'VPair', fst: Val, snd: Val };
export const VPair = (fst: Val, snd: Val): VPair => ({ tag: 'VPair', fst, snd });

export const VVar = (index: Ix): VNe => VNe(HVar(index), Nil);

export type EnvV = List<Val>;
export const extendV = (vs: EnvV, val: Val): EnvV => Cons(val, vs);
export const showEnvV = (l: EnvV, k: Ix = 0): string => listToString(l, v => showTerm(quote(v, k)));

export const vapp = (a: Val, b: Val): Val => {
  if (a.tag === 'VAbs') return a.body(b);
  if (a.tag === 'VNe') return VNe(a.head, Cons(EApp(b), a.args));
  return impossible(`pure vapp: ${a.tag}`);
};
export const vinc = (a: Val): Val => {
  if (a.tag === 'VNum') return VNum(a.value + 1);
  if (a.tag === 'VNe') return VNe(a.head, Cons(EInc, a.args));
  return impossible(`pure vinc: ${a.tag}`);
};

export const evaluate = (t: Term, vs: EnvV): Val => {
  if (t.tag === 'Var')
    return index(vs, t.index) || impossible(`evaluate ${t.index}`);
  if (t.tag === 'App')
    return vapp(evaluate(t.left, vs), evaluate(t.right, vs));
  if (t.tag === 'Abs')
    return VAbs(v => evaluate(t.body, extendV(vs, v)));
  if (t.tag === 'Num') return VNum(t.value);
  if (t.tag === 'Inc') return vinc(evaluate(t.term, vs));
  if (t.tag === 'Pair') return VPair(evaluate(t.fst, vs), evaluate(t.snd, vs));
  return t;
};

const quoteElim = (t: Term, e: Elim, k: Ix): Term => {
  if (e.tag === 'EApp') return App(t, quote(e.arg, k));
  if (e.tag === 'EInc') return Inc(t);
  return e;
};
export const quote = (v: Val, k: Ix): Term => {
  if (v.tag === 'VNe')
    return foldr(
      (x, y) => quoteElim(y, x, k),
      Var(k - (v.head.index + 1)) as Term,
      v.args,
    );
  if (v.tag === 'VAbs')
    return Abs(quote(v.body(VVar(k)), k + 1));
  if (v.tag === 'VNum') return Num(v.value);
  if (v.tag === 'VPair') return Pair(quote(v.fst, k), quote(v.snd, k));
  return v;
};

export const normalize = (t: Term, vs: EnvV = Nil, k: Ix = 0): Term =>
  quote(evaluate(t, vs), k);

import { Term, Pi, Type, App, Var, shift, Abs } from './syntax';
import { Val, force, quote, VVar } from './domain';
import { Ix, Name } from './names';
import { impossible } from './utils/util';
import { isEmpty, Nil, List, Cons, foldr } from './utils/list';

export const makeInductionPrinciple = (k: Ix, v_: Val, x: Term): Term => {
  const ty = quote(v_, k, 0);
  const v = force(v_);
  if (v.tag === 'VPi' && v.plicity && force(v.type).tag === 'VType')
    return Pi(v.plicity, 'P', Pi(false, '_', ty, Type), makeInductionPrincipleCon(k + 1, k, 0, v.body(VVar(k)), x, v_));
  return impossible(`makeInductionPrinciple ${v.tag}`);
};

const makeInductionPrincipleCon = (k: Ix, t: Ix, cons: number, v_: Val, x: Term, ty: Val): Term => {
  const v = force(v_);
  if (v.tag === 'VNe' && v.head.tag === 'HVar' && v.head.index === t && isEmpty(v.args))
    return App(Var(k - (t + 1)), false, shift(1 + cons, 0, x));
  if (v.tag === 'VPi' && !v.plicity)
    return Pi(false, v.name, makeInductionPrincipleCon2(k, t, cons, 0, Nil, v.type, x, ty), makeInductionPrincipleCon(k + 1, t, cons + 1, v.body(VVar(k)), x, ty));
  return impossible(`makeInductionPrincipleCon ${v.tag}`);
};

const makeInductionPrincipleCon2 = (k: Ix, t: Ix, cons: number, args: number, plics: List<boolean>, v_: Val, x: Term, ty: Val): Term => {
  const v = force(v_);
  if (v.tag === 'VNe' && v.head.tag === 'HVar' && v.head.index === t && isEmpty(v.args))
    return App(Var(k - (t + 1)), false, makeInductionPrincipleCon3(k, t, t, cons, 0, args, plics, x, ty));
  if (v.tag === 'VPi')
    return Pi(v.plicity, name(v.name, 'x', args), quote(v.type, k, 0), makeInductionPrincipleCon2(k + 1, t, cons, args + 1, Cons(v.plicity, plics), v.body(VVar(k)), x, ty));
  return impossible(`makeInductionPrincipleCon2 ${v.tag}`);
};

const makeInductionPrincipleCon3 = (ok: Ix, k: Ix, t: Ix, i: number, cons: number, args: number, plics: List<boolean>, x: Term, v_: Val): Term => {
  const v = force(v_);
  if (v.tag === 'VNe' && v.head.tag === 'HVar' && v.head.index === t && isEmpty(v.args))
    return foldr((pl, y, i) => App(y, pl, Var(i + cons)), Var(cons - 1 - i - 1) as Term, plics);
  if (v.tag === 'VPi')
    return Abs(v.plicity, name(v.name, 'a', cons - 1), shift(i + args + 1, cons, quote(v.type, k, 0)), makeInductionPrincipleCon3(ok + 1, k + 1, t, i, cons + 1, args, plics, x, v.body(VVar(k))));
  return impossible(`makeInductionPrincipleCon3 ${v.tag}`);
};

const name = (y: Name, x: Name, i: number): Name => y === '_' ? `${x}${i}` : y;

import { terr, impossible } from './utils/util';
import { showTermQ, VVar, vapp, Val, Elim, Head, showElimQ, forceGlue, quote, evaluate } from './domain';
import { forceLazy } from './utils/lazy';
import { zipWithR_, length, List, listToString, contains, indexOf, Cons, toArray, map, foldl, Nil } from './utils/list';
import { Ix, Name } from './names';
import { log } from './config';
import { metaPop, metaDiscard, metaPush, metaSet } from './metas';
import { Term, Var, showTerm, Pi, Abs, App, Type, Data, Con, Case } from './syntax';
import { Plicity } from './surface';

const eqHead = (a: Head, b: Head): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.index === b.index;
  if (a.tag === 'HGlobal') return b.tag === 'HGlobal' && a.name === b.name;
  if (a.tag === 'HMeta') return b.tag === 'HMeta' && a.index === b.index;
  return a;
};
const unifyElim = (k: Ix, a: Elim, b: Elim, x: Val, y: Val): void => {
  if (a === b) return;
  if (a.tag === 'EApp' && b.tag === 'EApp' && a.plicity === b.plicity)
    return unify(k, a.arg, b.arg);
  if (a.tag === 'ECase' && b.tag === 'ECase' && a.cases.length === b.cases.length) {
    unify(k, a.type, b.type);
    unify(k, a.prop, b.prop);
    const l = a.cases.length;
    for (let i = 0; i < l; i++) unify(k + 1, a.cases[i], b.cases[i]);
    return;
  }
  return terr(`unify failed (${k}): ${showTermQ(x, k)} ~ ${showTermQ(y, k)}`);
};
export const unify = (k: Ix, a_: Val, b_: Val): void => {
  const a = forceGlue(a_);
  const b = forceGlue(b_);
  log(() => `unify(${k}) ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
  if (a === b) return;
  if (a.tag === 'VType' && b.tag === 'VType') return;
  if (a.tag === 'VCon' && b.tag === 'VCon' && a.index === b.index && a.total === b.total && a.args.length === b.args.length) {
    unify(k, a.type, b.type);
    const l = a.args.length;
    for (let i = 0; i < l; i++) {
      if (a.args[i][1] !== b.args[i][1])
        return terr(`unify failed (${k}): ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
      unify(k, a.args[i][0], b.args[i][0]);
    }
    return;
  }
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.plicity === b.plicity) {
    unify(k, a.type, b.type);
    const v = VVar(k);
    return unify(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VData' && b.tag === 'VData' && a.cons.length === b.cons.length) {
    const v = VVar(k);
    const l = a.cons.length;
    for (let i = 0; i < l; i++) unify(k + 1, a.cons[i](v), b.cons[i](v));
    return;
  }
  if (a.tag === 'VAbs' && b.tag === 'VAbs' && a.plicity === b.plicity) {
    unify(k, a.type, b.type);
    const v = VVar(k);
    return unify(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VAbs') {
    const v = VVar(k);
    return unify(k + 1, a.body(v), vapp(b, a.plicity, v));
  }
  if (b.tag === 'VAbs') {
    const v = VVar(k);
    return unify(k + 1, vapp(a, b.plicity, v), b.body(v));
  }
  if (a.tag === 'VNe' && b.tag === 'VNe' && eqHead(a.head, b.head) && length(a.args) === length(b.args))
    return zipWithR_((x, y) => unifyElim(k, x, y, a, b), a.args, b.args);
  if (a.tag === 'VNe' && b.tag === 'VNe' && a.head.tag === 'HMeta' && b.head.tag === 'HMeta')
    return length(a.args) > length(b.args) ?
      solve(k, a.head.index, a.args, b) :
      solve(k, b.head.index, b.args, a);
  if (a.tag === 'VNe' && a.head.tag === 'HMeta')
    return solve(k, a.head.index, a.args, b);
  if (b.tag === 'VNe' && b.head.tag === 'HMeta')
    return solve(k, b.head.index, b.args, a);
  if (a.tag === 'VGlued' && b.tag === 'VGlued' && eqHead(a.head, b.head) && length(a.args) === length(b.args)) {
    try {
      metaPush();
      zipWithR_((x, y) => unifyElim(k, x, y, a, b), a.args, b.args);
      metaDiscard();
      return;
    } catch(err) {
      if (!(err instanceof TypeError)) throw err;
      metaPop();
      return unify(k, forceLazy(a.val), forceLazy(b.val));
    }
  }
  if (a.tag === 'VGlued') return unify(k, forceLazy(a.val), b);
  if (b.tag === 'VGlued') return unify(k, a, forceLazy(b.val));
  return terr(`unify failed (${k}): ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
};

const solve = (k: Ix, m: Ix, spine: List<Elim>, val: Val): void => {
  log(() => `solve ?${m} ${listToString(spine, e => showElimQ(e, k))} := ${showTermQ(val, k)} (${k})`);
  try {
    const spinex = checkSpine(k, spine);
    const rhs = quote(val, k, 0);
    const ivs = map(spinex, ([_, v]) => v);
    const body = checkSolution(k, m, ivs, rhs);
    // Note: I'm solving with an abstraction that has * as type for all the parameters
    // TODO: I think it might actually matter
    log(() => `spine ${listToString(spinex, ([p, s]) => `${p ? '-' : ''}${s}`)}`);
    const solution = foldl((body, [pl, y]) => {
      if (typeof y === 'string') return Abs(pl, '_', Type, body);
      return Abs(pl, '_', Type, body);
    }, body, spinex);
    log(() => `solution ?${m} := ${showTerm(solution)} | ${showTerm(solution)}`);
    const vsolution = evaluate(solution, Nil);
    metaSet(m, vsolution);
  } catch (err) {
    if (!(err instanceof TypeError)) throw err;
    const a = toArray(spine, e => showElimQ(e, k));
    return terr(`failed to solve meta (?${m}${a.length > 0 ? ' ': ''}${a.join(' ')}) := ${showTermQ(val, k)}: ${err.message}`);
  }
};

const checkSpine = (k: Ix, spine: List<Elim>): List<[Plicity, Ix | Name]> =>
  map(spine, elim => {
    if (elim.tag === 'ECase') return terr(`case in meta spine`);
    if (elim.tag === 'EApp') {
      const v = forceGlue(elim.arg);
      if ((v.tag === 'VNe' || v.tag === 'VGlued') && v.head.tag === 'HVar' && length(v.args) === 0)
        return [elim.plicity, v.head.index];
      if ((v.tag === 'VNe' || v.tag === 'VGlued') && v.head.tag === 'HGlobal' && length(v.args) === 0)
        return [elim.plicity, v.head.name];
      return terr(`not a var in spine: ${showTermQ(v, k)}`);
    }
    return elim;
  });

const checkSolution = (k: Ix, m: Ix, is: List<Ix | Name>, t: Term): Term => {
  if (t.tag === 'Type') return t;
  if (t.tag === 'Global') return t;
  if (t.tag === 'Var') {
    const i = k - t.index - 1;
    if (contains(is, i))
      return Var(indexOf(is, i));
    return terr(`scope error ${t.index} (${i})`);
  }
  if (t.tag === 'Meta') {
    if (m === t.index)
      return terr(`occurs check failed: ${showTerm(t)}`);
    return t;
  }
  if (t.tag === 'App') {
    const l = checkSolution(k, m, is, t.left);
    const r = checkSolution(k, m, is, t.right);
    return App(l, t.plicity, r);
  }
  if (t.tag === 'Abs' && t.type) {
    const ty = checkSolution(k, m, is, t.type);
    const body = checkSolution(k + 1, m, Cons(k, is), t.body);
    return Abs(t.plicity, t.name, ty, body);
  }
  if (t.tag === 'Pi') {
    const ty = checkSolution(k, m, is, t.type);
    const body = checkSolution(k + 1, m, Cons(k, is), t.body);
    return Pi(t.plicity, t.name, ty, body);
  }
  if (t.tag === 'Data')
    return Data(t.name, t.cons.map(x => checkSolution(k + 1, m, Cons(k, is), x)));
  if (t.tag === 'Con' && t.type) {
    const ty = checkSolution(k, m, is, t.type);
    const args: [Term, Plicity][] = t.args.map(([t, p]) => [checkSolution(k, m, is, t), p]);
    return Con(ty, t.index, t.total, args);
  }
  if (t.tag === 'Case') {
    const type = checkSolution(k, m, is, t.type);
    const prop = checkSolution(k, m, is, t.type);
    const scrut = checkSolution(k, m, is, t.type);
    const cases: Term[] = t.cases.map(t => checkSolution(k, m, is, t));
    return Case(type, prop, scrut, cases);
  }
  return impossible(`checkSolution ?${m}: non-normal term: ${showTerm(t)}`);
};

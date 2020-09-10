import { terr, impossible, hasDuplicates } from './utils/utils';
import { showTermQ, VVar, vapp, Val, Elim, showElimQ, forceGlue, quote, evaluate, vproj, VNatLit, VNe } from './domain';
import { forceLazy } from './utils/lazy';
import { zipWithR_, length, List, listToString, contains, indexOf, Cons, toArray, map, foldl, Nil } from './utils/list';
import { Ix, Name } from './names';
import { log } from './config';
import { metaPop, metaDiscard, metaPush, metaSet } from './metas';
import { Term, Var, showTerm, Pi, Abs, App, Type, Sigma, Pair, Proj, Data, TCon, Con, DElim, FinLit } from './syntax';
import { Plicity } from './surface';
import { eqHead } from './conv';

const unifyElim = (k: Ix, a: Elim, b: Elim, x: Val, y: Val): void => {
  if (a === b) return;
  if (a.tag === 'ES' && b.tag === 'ES') return;
  if (a.tag === 'EFS' && b.tag === 'EFS') return;
  if (a.tag === 'EApp' && b.tag === 'EApp' && a.plicity === b.plicity)
    return unify(k, a.arg, b.arg);
  if (a.tag === 'EProj' && b.tag === 'EProj' && a.proj === b.proj) return;
  if (a.tag === 'EElimHEq' && b.tag === 'EElimHEq' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      unify(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EElim' && b.tag === 'EElim' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      unify(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EIndNat' && b.tag === 'EIndNat' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      unify(k, a.args[i], b.args[i]);
    return;
  }
  return terr(`unify elim failed (${k}): ${showTermQ(x, k)} ~ ${showTermQ(y, k)}`);
};
export const unify = (k: Ix, a_: Val, b_: Val): void => {
  const a = forceGlue(a_);
  const b = forceGlue(b_);
  log(() => `unify(${k}) ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
  if (a === b) return;
  if (a.tag === 'VSort' && b.tag === 'VSort' && a.sort === b.sort) return;
  if (a.tag === 'VNatLit' && b.tag === 'VNatLit' && a.val === b.val) return;
  if (a.tag === 'VFinLit' && b.tag === 'VFinLit' && a.index === b.index) return;
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.plicity === b.plicity) {
    unify(k, a.type, b.type);
    const v = VVar(k);
    return unify(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.plicity === b.plicity && a.plicity2 === b.plicity2) {
    unify(k, a.type, b.type);
    const v = VVar(k);
    return unify(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VPair' && b.tag === 'VPair' && a.plicity === b.plicity && a.plicity2 === b.plicity2) {
    unify(k, a.fst, b.fst);
    unify(k, a.snd, b.snd);
    return unify(k, a.type, b.type);
  }
  if (a.tag === 'VAbs' && b.tag === 'VAbs' && a.plicity === b.plicity) {
    unify(k, a.type, b.type);
    const v = VVar(k);
    return unify(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VData' && b.tag === 'VData' && a.cons.length === b.cons.length) {
    unify(k, a.index, b.index);
    for (let i = 0, l = a.cons.length; i < l; i++)
      unify(k, a.cons[i], b.cons[i]);
    return;
  }
  if (a.tag === 'VTCon' && b.tag === 'VTCon') {
    unify(k, a.data, b.data);
    unify(k, a.arg, b.arg);
    return;
  }
  if (a.tag === 'VCon' && b.tag === 'VCon' && a.index === b.index) {
    unify(k, a.data, b.data);
    unify(k, a.arg, b.arg);
    return;
  }
  // eta
  if (a.tag === 'VAbs') {
    const v = VVar(k);
    return unify(k + 1, a.body(v), vapp(b, a.plicity, v));
  }
  if (b.tag === 'VAbs') {
    const v = VVar(k);
    return unify(k + 1, vapp(a, b.plicity, v), b.body(v));
  }
  if (a.tag === 'VPair') {
    unify(k, a.fst, vproj('fst', b));
    return unify(k, a.snd, vproj('snd', b));
  }
  if (b.tag === 'VPair') {
    unify(k, vproj('fst', a), b.fst);
    return unify(k, vproj('snd', a), b.snd);
  }
  if (a.tag === 'VNe' && a.head.tag === 'HPrim' && a.head.name === 'Unit') return;
  if (b.tag === 'VNe' && b.head.tag === 'HPrim' && b.head.name === 'Unit') return;

  // nat extra rules (are they needed?)
  if (a.tag === 'VNe' && a.args.tag === 'Cons' && a.args.head.tag === 'ES' && b.tag === 'VNatLit' && b.val > 0)
    return unify(k, VNe(a.head, a.args.tail), VNatLit(b.val - 1n));
  if (a.tag === 'VNatLit' && a.val > 0 && b.tag === 'VNe' && b.args.tag === 'Cons' && b.args.head.tag === 'ES')
    return unify(k, VNatLit(a.val - 1n), VNe(b.head, b.args.tail));

  // TODO: fin rules
  if (a.tag === 'VFinLit' && a.index === 0n && a.cap.tag === 'VNatLit' && a.cap.val === 0n) return;
  if (b.tag === 'VFinLit' && b.index === 0n && b.cap.tag === 'VNatLit' && b.cap.val === 0n) return;

  // neutrals
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
    if (hasDuplicates(toArray(spinex, x => x)))
      return terr(`meta spine contains duplicates`);
    const rhs = quote(val, k, false);
    const ivs = map(spinex, ([_, v]) => v);
    const body = checkSolution(k, m, ivs, rhs);
    // Note: I'm solving with an abstraction that has * as type for all the parameters
    // TODO: I think it might actually matter
    log(() => `spine ${listToString(spinex, ([p, s]) => `${p ? '-' : ''}${s}`)}`);
    const solution = foldl((body, [pl, y]) => {
      if (typeof y === 'string') return Abs(pl, `${y}\$`, Type, body);
      return Abs(pl, '$', Type, body);
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
    if (elim.tag === 'EApp') {
      const v = forceGlue(elim.arg);
      if ((v.tag === 'VNe' || v.tag === 'VGlued') && v.head.tag === 'HVar' && length(v.args) === 0)
        return [elim.plicity, v.head.index];
      if ((v.tag === 'VNe' || v.tag === 'VGlued') && v.head.tag === 'HGlobal' && length(v.args) === 0)
        return [elim.plicity, v.head.name];
      if ((v.tag === 'VNe' || v.tag === 'VGlued') && v.head.tag === 'HPrim' && length(v.args) === 0)
        return [elim.plicity, v.head.name];
      return terr(`not a var in spine: ${showTermQ(v, k)}`);
    }
    return terr(`unexpected elim in meta spine: ${elim.tag}`);
  });

const checkSolution = (k: Ix, m: Ix, is: List<Ix | Name>, t: Term): Term => {
  if (t.tag === 'Prim') return t;
  if (t.tag === 'Sort') return t;
  if (t.tag === 'NatLit') return t;
  if (t.tag === 'Var') {
    const i = k - t.index - 1;
    if (contains(is, i))
      return Var(indexOf(is, i));
    return terr(`scope error ${t.index} (${i})`);
  }
  if (t.tag === 'Global') {
    if (contains(is, t.name))
      return Var(indexOf(is, t.name));
    return t;
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
  if (t.tag === 'Pair') {
    const l = checkSolution(k, m, is, t.fst);
    const r = checkSolution(k, m, is, t.snd);
    const ty = checkSolution(k, m, is, t.type);
    return Pair(t.plicity, t.plicity2, l, r, ty);
  }
  if (t.tag === 'Proj') {
    const x = checkSolution(k, m, is, t.term);
    return Proj(t.proj, x);
  }
  if (t.tag === 'Abs') {
    const ty = checkSolution(k, m, is, t.type);
    const body = checkSolution(k + 1, m, Cons(k, is), t.body);
    return Abs(t.plicity, t.name, ty, body);
  }
  if (t.tag === 'Pi') {
    const ty = checkSolution(k, m, is, t.type);
    const body = checkSolution(k + 1, m, Cons(k, is), t.body);
    return Pi(t.plicity, t.name, ty, body);
  }
  if (t.tag === 'Sigma') {
    const ty = checkSolution(k, m, is, t.type);
    const body = checkSolution(k + 1, m, Cons(k, is), t.body);
    return Sigma(t.plicity, t.plicity2, t.name, ty, body);
  }
  if (t.tag === 'Data') {
    const index = checkSolution(k, m, is, t.index);
    const cons = t.cons.map(x => checkSolution(k, m, is, x));
    return Data(index, cons);
  }
  if (t.tag === 'TCon') {
    const data = checkSolution(k, m, is, t.data);
    const arg = checkSolution(k, m, is, t.arg);
    return TCon(data, arg);
  }
  if (t.tag === 'Con') {
    const data = checkSolution(k, m, is, t.data);
    const arg = checkSolution(k, m, is, t.arg);
    return Con(t.index, data, arg);
  }
  if (t.tag === 'DElim') {
    const data = checkSolution(k, m, is, t.data);
    const motive = checkSolution(k, m, is, t.motive);
    const index = checkSolution(k, m, is, t.index);
    const scrut = checkSolution(k, m, is, t.scrut);
    const args = t.args.map(x => checkSolution(k, m, is, x));
    return DElim(data, motive, index, scrut, args);
  }
  if (t.tag === 'FinLit') {
    const cap = checkSolution(k, m, is, t.cap);
    return FinLit(t.index, cap);
  }
  return impossible(`checkSolution ?${m}: non-normal term: ${showTerm(t)}`);
};

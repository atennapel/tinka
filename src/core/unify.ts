import { terr } from '../utils/util';
import { showTermQ, VVar, vapp, Val, Elim, Head } from './domain';
import { forceLazy } from '../utils/lazy';
import { zipWithR_, length } from '../utils/list';
import { Ix } from '../names';
import { log } from '../config';

const eqHead = (a: Head, b: Head): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.index === b.index;
  if (a.tag === 'HGlobal') return b.tag === 'HGlobal' && a.name === b.name;
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
export const unify = (k: Ix, a: Val, b: Val): void => {
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
  if (a.tag === 'VGlued' && b.tag === 'VGlued' && eqHead(a.head, b.head) && length(a.args) === length(b.args)) {
    try {
      return zipWithR_((x, y) => unifyElim(k, x, y, a, b), a.args, b.args);
    } catch(err) {
      if (!(err instanceof TypeError)) throw err;
      return unify(k, forceLazy(a.val), forceLazy(b.val));
    }
  }
  if (a.tag === 'VGlued') return unify(k, forceLazy(a.val), b);
  if (b.tag === 'VGlued') return unify(k, a, forceLazy(b.val));
  return terr(`unify failed (${k}): ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
};

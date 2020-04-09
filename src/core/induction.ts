import { Val, force, VVar, quote, VPi, VType, vapp, VAbs, VRoll, VFix, VNe, VGlued, Head, Elim, EApp, HVar } from './domain';
import { Ix } from '../names';
import { terr } from '../utils/util';
import { isEmpty, map } from '../utils/list';
import { showTerm } from './syntax';
import { mapLazy } from '../utils/lazy';

export const makeInductionPrinciple = (k: Ix, v_: Val, x: Val): Val => {
  const v = force(v_);
  if (v.tag === 'VPi' && v.plicity)
    return VPi(true, VPi(false, v_, _ => VType), P => makeInductionPrincipleR(k, v_, k + 1, k, P, 0, x, v.body(VVar(k))));
  return terr(`failed to generate induction principle for ${showTerm(quote(v_, k, false))}`);
};

const makeInductionPrincipleR = (ik: Ix, T: Val, k: Ix, t: Ix, P: Val, i: number, x: Val, v_: Val): Val => {
  const v = force(v_);
  if (v.tag === 'VNe' && v.head.tag === 'HVar' && v.head.index === t && isEmpty(v.args))
    return vapp(P, false, x);
  if (v.tag === 'VPi' && !v.plicity)
    return VPi(false, makeInductionPrincipleC(ik, T, k, t, P, i, x, 0, v.type), _ => makeInductionPrincipleR(ik, T, k + 1, t, P, i + 1, x, v.body(VVar(k))));
  return terr(`failed to generate induction principle (R) for ${showTerm(quote(v_, k, false))}`);
};

const makeInductionPrincipleC = (ik: Ix, T: Val, k: Ix, t: Ix, P: Val, i: number, x: Val, args: number, v_: Val): Val => {
  const v = force(v_);
  if (v.tag === 'VNe' && v.head.tag === 'HVar' && v.head.index === t && isEmpty(v.args))
    return vapp(P, false, makeInductionPrincipleCon(ik, ik, t, P, i, 0, x, args, T));
  if (v.tag === 'VPi')
    return VPi(v.plicity, v.type, _ => makeInductionPrincipleC(ik, T, k + 1, t, P, i, x, args + 1, v.body(VVar(k))));
  return terr(`failed to generate induction principle (C) for ${showTerm(quote(v_, k, false))}`);
};

const makeInductionPrincipleCon = (ok: Ix, k: Ix, t: Ix, P: Val, i: number, i2: number, x: Val, args: number, v_: Val): Val => {
  const v = force(v_);
  if (v.tag === 'VNe' && v.head.tag === 'HVar' && v.head.index === t && isEmpty(v.args))
    return [VVar(k + i*2 - i2 + 2 + args) as Val].concat(Array.from({ length: args }, (_, j) => VVar(k + i - i2 + args - j)).reverse()).reduce((x, y) => vapp(x, false, y));
  if (v.tag === 'VPi')
    return VAbs(v.plicity, shift(args + i + 1, ok, v.type), _ => makeInductionPrincipleCon(ok, k + 1, t, P, i, i2 + 1, x, args, v.body(VVar(k))));
  return terr(`failed to generate induction principle (Con) for ${showTerm(quote(v, k, false))}`);
};

const shiftHead = (d: Ix, c: Ix, h: Head): Head => {
  if (h.tag === 'HGlobal') return h;
  if (h.tag === 'HVar') return h.index < c ? h : HVar(h.index + d);
  return h;
};
const shiftElim = (d: Ix, c: Ix, e: Elim): Elim => {
  if (e.tag === 'EApp') return EApp(e.plicity, shift(d, c, e.arg));
  if (e.tag === 'EUnroll') return e;
  return e;
};
const shift = (d: Ix, c: Ix, v: Val): Val => {
  if (v.tag === 'VType') return v;
  if (v.tag === 'VNe')
    return VNe(shiftHead(d, c, v.head), map(v.args, x => shiftElim(d, c, x)));
  if (v.tag === 'VGlued')
    return VGlued(shiftHead(d, c, v.head), map(v.args, x => shiftElim(d, c, x)), mapLazy(v.val, x => shift(d, c, x)));
  if (v.tag === 'VAbs')
    return VAbs(v.plicity, shift(d, c, v.type), x => shift(d, c, v.body(x)));
  if (v.tag === 'VPi')
    return VPi(v.plicity, shift(d, c, v.type), x => shift(d, c, v.body(x)));
  if (v.tag === 'VFix')
    return VFix(shift(d, c, v.type), x => shift(d, c, v.body(x)));
  if (v.tag === 'VRoll')
    return VRoll(shift(d, c, v.type), shift(d, c, v.term));
  return v;
};

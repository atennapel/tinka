import { terr } from './utils/utils';
import { showTermQ, VVar, vapp, Val, Elim, Head, forceGlue, vproj } from './domain';
import { forceLazy } from './utils/lazy';
import { zipWithR_, length } from './utils/list';
import { Ix } from './names';
import { log } from './config';

export const eqHead = (a: Head, b: Head): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.index === b.index;
  if (a.tag === 'HGlobal') return b.tag === 'HGlobal' && a.name === b.name;
  if (a.tag === 'HMeta') return b.tag === 'HMeta' && a.index === b.index;
  if (a.tag === 'HPrim') return b.tag === 'HPrim' && a.name === b.name;
  return a;
};
const convElim = (k: Ix, a: Elim, b: Elim, x: Val, y: Val): void => {
  if (a === b) return;
  if (a.tag === 'EApp' && b.tag === 'EApp' && a.plicity === b.plicity)
    return conv(k, a.arg, b.arg);
  if (a.tag === 'EUnsafeCast' && b.tag === 'EUnsafeCast')
    return conv(k, a.type, b.type);
  if (a.tag === 'EProj' && b.tag === 'EProj' && a.proj === b.proj) return;
  if (a.tag === 'EIFixInd' && b.tag === 'EIFixInd' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      conv(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EElimHEq' && b.tag === 'EElimHEq' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      conv(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EIndUnit' && b.tag === 'EIndUnit' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      conv(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EIndBool' && b.tag === 'EIndBool' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      conv(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EIndType' && b.tag === 'EIndType' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      conv(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'EIndNat' && b.tag === 'EIndNat' && a.args.length === b.args.length) {
    for (let i = 0; i < a.args.length; i ++)
      conv(k, a.args[i], b.args[i]);
    return;
  }
  if (a.tag === 'ENatBinop' && b.tag === 'ENatBinop' && a.op === b.op) return conv(k, a.arg, b.arg);
  return terr(`conv failed (${k}): ${showTermQ(x, k)} ~ ${showTermQ(y, k)}`);
};
export const conv = (k: Ix, a_: Val, b_: Val): void => {
  const a = forceGlue(a_);
  const b = forceGlue(b_);
  log(() => `conv(${k}) ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
  if (a === b) return;
  if (a.tag === 'VType' && b.tag === 'VType') return;
  if (a.tag === 'VNat' && b.tag === 'VNat' && a.val === b.val) return;
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.plicity === b.plicity) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.plicity === b.plicity && a.plicity2 === b.plicity2) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VPair' && b.tag === 'VPair' && a.plicity === b.plicity && a.plicity2 === b.plicity2) {
    conv(k, a.fst, b.fst);
    conv(k, a.snd, b.snd);
    return conv(k, a.type, b.type);
  }
  if (a.tag === 'VAbs' && b.tag === 'VAbs' && a.plicity === b.plicity) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, a.body(v), b.body(v));
  }
  if (a.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, a.body(v), vapp(b, a.plicity, v));
  }
  if (b.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vapp(a, b.plicity, v), b.body(v));
  }
  if (a.tag === 'VPair') {
    conv(k, a.fst, vproj('fst', b));
    return conv(k, a.snd, vproj('snd', b));
  }
  if (b.tag === 'VPair') {
    conv(k, vproj('fst', a), b.fst);
    return conv(k, vproj('snd', a), b.snd);
  }
  if (a.tag === 'VNe' && a.head.tag === 'HPrim' && a.head.name === 'Unit') return;
  if (b.tag === 'VNe' && b.head.tag === 'HPrim' && b.head.name === 'Unit') return;
  if (a.tag === 'VNe' && b.tag === 'VNe' && eqHead(a.head, b.head) && length(a.args) === length(b.args))
    return zipWithR_((x, y) => convElim(k, x, y, a, b), a.args, b.args);
  if (a.tag === 'VGlued' && b.tag === 'VGlued' && eqHead(a.head, b.head) && length(a.args) === length(b.args)) {
    try {
      return zipWithR_((x, y) => convElim(k, x, y, a, b), a.args, b.args);
    } catch(err) {
      if (!(err instanceof TypeError)) throw err;
      return conv(k, forceLazy(a.val), forceLazy(b.val));
    }
  }
  if (a.tag === 'VGlued') return conv(k, forceLazy(a.val), b);
  if (b.tag === 'VGlued') return conv(k, a, forceLazy(b.val));
  return terr(`conv failed (${k}): ${showTermQ(a, k)} ~ ${showTermQ(b, k)}`);
};

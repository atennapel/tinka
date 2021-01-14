import { log } from './config';
import { PFst, PSnd } from './core';
import { eqMode } from './mode';
import { Ix, Lvl } from './names';
import { terr, tryT } from './utils/utils';
import { Head, Val, show, VVar, vinst, vapp, vproj, Spine } from './values';

export const eqHead = (a: Head, b: Head): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.level === b.level;
  if (a.tag === 'HPrim') return b.tag === 'HPrim' && a.name === b.name;
  return a;
};
const convPIndex = (k: Lvl, va: Val, vb: Val, sa: Spine, sb: Spine, index: Ix): void => {
  if (index === 0) return convSpines(k, va, vb, sa, sb);
  if (sa.isCons() && sa.head.tag === 'EProj' && sa.head.proj.tag === 'PProj' && sa.head.proj.proj === 'snd')
    return convPIndex(k, va, vb, sa.tail, sb, index - 1);
  return terr(`conv failed (${k}): ${show(va, k)} ~ ${show(vb, k)}`);
}; 
const convSpines = (k: Lvl, va: Val, vb: Val, sa: Spine, sb: Spine): void => {
  if (sa.isNil() && sb.isNil()) return;
  if (sa.isCons() && sb.isCons()) {
    const a = sa.head;
    const b = sb.head;
    if (a === b) return convSpines(k, va, vb, sa.tail, sb.tail);
    if (a.tag === 'EApp' && b.tag === 'EApp' && eqMode(a.mode, b.mode)) {
      conv(k, a.arg, b.arg);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EElimSigma' && b.tag === 'EElimSigma' && a.usage === b.usage) {
      conv(k, a.motive, b.motive);
      conv(k, a.cas, b.cas);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EElimPropEq' && b.tag === 'EElimPropEq' && a.usage === b.usage) {
      conv(k, a.motive, b.motive);
      conv(k, a.cas, b.cas);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EElimBool' && b.tag === 'EElimBool' && a.usage === b.usage) {
      conv(k, a.motive, b.motive);
      conv(k, a.trueBranch, b.trueBranch);
      conv(k, a.falseBranch, b.falseBranch);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EProj' && b.tag === 'EProj') {
      if (a.proj === b.proj)
        return convSpines(k, va, vb, sa.tail, sb.tail);
      if (a.proj.tag === 'PProj' && b.proj.tag === 'PProj' && a.proj.proj === b.proj.proj)
        return convSpines(k, va, vb, sa.tail, sb.tail);
      if (a.proj.tag === 'PIndex' && b.proj.tag === 'PIndex' && a.proj.index === b.proj.index)
        return convSpines(k, va, vb, sa.tail, sb.tail);
      if (a.proj.tag === 'PProj' && a.proj.proj === 'fst' && b.proj.tag === 'PIndex')
        return convPIndex(k, va, vb, sa.tail, sb.tail, b.proj.index);
      if (b.proj.tag === 'PProj' && b.proj.proj === 'fst' && a.proj.tag === 'PIndex')
        return convPIndex(k, va, vb, sb.tail, sa.tail, a.proj.index);
    }
  }
  return terr(`conv failed (${k}): ${show(va, k)} ~ ${show(vb, k)}`);
};
export const conv = (k: Lvl, a: Val, b: Val): void => {
  log(() => `conv(${k}): ${show(a, k)} ~ ${show(b, k)}`);
  if (a === b) return;
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.usage === b.usage && eqMode(a.mode, b.mode)) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.usage === b.usage && a.exclusive === b.exclusive) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VPropEq' && b.tag === 'VPropEq') {
    conv(k, a.type, b.type);
    conv(k, a.left, b.left);
    return conv(k, a.right, b.right);
  }
  if (a.tag === 'VAbs' && b.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VPair' && b.tag === 'VPair') {
    conv(k, a.fst, b.fst);
    return conv(k, a.snd, b.snd);
  }
  if (a.tag === 'VRefl' && b.tag === 'VRefl') {
    conv(k, a.type, b.type);
    return conv(k, a.val, b.val);
  }

  if (a.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vapp(b, a.mode, v));
  }
  if (b.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vapp(a, b.mode, v), vinst(b, v));
  }

  // TODO: is this correct for linear/erased sigmas?
  if (a.tag === 'VPair') {
    conv(k, a.fst, vproj(b, PFst));
    conv(k, a.snd, vproj(b, PSnd));
    return;
  }
  if (b.tag === 'VPair') {
    conv(k, vproj(a, PFst), b.fst);
    conv(k, vproj(a, PSnd), b.snd);
    return;
  }

  if (a.tag === 'VNe' && b.tag === 'VNe' && eqHead(a.head, b.head))
    return convSpines(k, a, b, a.spine, b.spine);

  if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && a.head === b.head)
    return tryT(() => convSpines(k, a, b, a.spine, b.spine), () => conv(k, a.val.get(), b.val.get()));
  if (a.tag === 'VGlobal') return conv(k, a.val.get(), b);
  if (b.tag === 'VGlobal') return conv(k, a, b.val.get());

  return terr(`conv failed (${k}): ${show(a, k)} ~ ${show(b, k)}`);
};

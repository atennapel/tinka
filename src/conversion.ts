import { log } from './config';
import { PFst, PSnd } from './core';
import { eqMode } from './mode';
import { Ix, Lvl } from './names';
import { terr, tryT } from './utils/utils';
import { Head, Val, show, VVar, vinst, vapp, vproj, Spine, vdecideS, vdecideFS } from './values';

export const eqHead = (a: Head, b: Head): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.level === b.level;
  return a.tag;
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
    if (a.tag === 'ENatS' && b.tag === 'ENatS') return convSpines(k, va, vb, sa.tail, sb.tail);
    if (a.tag === 'EFinS' && b.tag === 'EFinS') {
      conv(k, a.index, b.index);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
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
    if (a.tag === 'EElimNat' && b.tag === 'EElimNat' && a.usage === b.usage) {
      conv(k, a.motive, b.motive);
      conv(k, a.z, b.z);
      conv(k, a.s, b.s);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EElimFin' && b.tag === 'EElimFin' && a.usage === b.usage) {
      conv(k, a.motive, b.motive);
      conv(k, a.z, b.z);
      conv(k, a.s, b.s);
      return convSpines(k, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EElimFinN' && b.tag === 'EElimFinN' && a.usage === b.usage && a.cs.length === b.cs.length) {
      conv(k, a.motive, b.motive);
      for (let i = 0, l = a.cs.length; i < l; i++)
        conv(k, a.cs[i], b.cs[i]);
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
  if (a.tag === 'VType' && b.tag === 'VType') return;
  if (a.tag === 'VNat' && b.tag === 'VNat') return;
  if (a.tag === 'VNatLit' && b.tag === 'VNatLit' && a.value === b.value) return;
  if (a.tag === 'VFin' && b.tag === 'VFin') return conv(k, a.index, b.index);
  if (a.tag === 'VFinLit' && b.tag === 'VFinLit' && a.val === b.val) return conv(k, a.index, b.index);
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.usage === b.usage && eqMode(a.mode, b.mode)) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.usage === b.usage) {
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

  const n = vdecideS(a);
  const m = vdecideS(b);
  if (n && m) return conv(k, n, m);

  const fn = vdecideFS(a);
  const fm = vdecideFS(b);
  if (fn && fm) {
    conv(k, fn[1], fm[1]);
    return conv(k, fn[0], fm[0]);
  }

  if (a.tag === 'VNe' && b.tag === 'VNe' && eqHead(a.head, b.head))
    return convSpines(k, a, b, a.spine, b.spine);

  if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && a.head === b.head)
    return tryT(() => convSpines(k, a, b, a.spine, b.spine), () => conv(k, a.val.get(), b.val.get()));
  if (a.tag === 'VGlobal') return conv(k, a.val.get(), b);
  if (b.tag === 'VGlobal') return conv(k, a, b.val.get());

  return terr(`conv failed (${k}): ${show(a, k)} ~ ${show(b, k)}`);
};

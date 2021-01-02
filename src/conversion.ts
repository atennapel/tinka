import { log } from './config';
import { eqMode } from './mode';
import { Lvl } from './names';
import { terr, tryT } from './utils/utils';
import { Elim, Head, Val, show, VVar, vinst, vapp } from './values';

export const eqHead = (a: Head, b: Head): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.level === b.level;
  return a.tag;
};
const convElim = (k: Lvl, a: Elim, b: Elim, x: Val, y: Val): void => {
  if (a === b) return;
  if (a.tag === 'EApp' && b.tag === 'EApp' && eqMode(a.mode, b.mode)) return conv(k, a.arg, b.arg);
  return terr(`conv failed (${k}): ${show(x, k)} ~ ${show(y, k)}`);
};
export const conv = (k: Lvl, a: Val, b: Val): void => {
  log(() => `conv(${k}): ${show(a, k)} ~ ${show(b, k)}`);
  if (a === b) return;
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.usage === b.usage && eqMode(a.mode, b.mode)) {
    conv(k, a.type, b.type);
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VAbs' && b.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vinst(b, v));
  }

  if (a.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vinst(a, v), vapp(b, a.mode, v));
  }
  if (b.tag === 'VAbs') {
    const v = VVar(k);
    return conv(k + 1, vapp(a, b.mode, v), vinst(b, v));
  }

  if (a.tag === 'VNe' && b.tag === 'VNe' && eqHead(a.head, b.head))
    return a.spine.zipWithR_(b.spine, (x, y) => convElim(k, x, y, a, b));

  if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && a.head === b.head) {
    return tryT(() => a.spine.zipWithR_(b.spine, (x, y) => convElim(k, x, y, a, b)),
      () => conv(k, a.val.get(), b.val.get()));
  }
  if (a.tag === 'VGlobal') return conv(k, a.val.get(), b);
  if (b.tag === 'VGlobal') return conv(k, a, b.val.get());

  return terr(`conv failed (${k}): ${show(a, k)} ~ ${show(b, k)}`);
};
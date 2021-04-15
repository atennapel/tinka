import { config, log } from './config';
import { Abs, App, Core, Meta, Pi, Var, Global, Sigma, Pair, PFst, PSnd, Prim } from './core';
import { getMeta, MetaVar, setMeta } from './metas';
import { Ix, Lvl } from './names';
import { nil } from './utils/List';
import { impossible, terr, tryT } from './utils/utils';
import { force, isVVar, Spine, vinst, VVar, Val, evaluate, vapp, show, Elim, vproj, Head, GHead, getVPrim, quote, VNatLit, VRigid, VFlex, VFinLit, vpred } from './values';
import * as C from './core';
import { eqMode, Expl } from './mode';
import { verify } from './verification';
import { Local } from './local';

type IntMap<T> = { [key: number]: T };
const insert = <T>(map: IntMap<T>, key: number, value: T): IntMap<T> =>
  ({ ...map, [key]: value });

interface PartialRenaming {
  readonly dom: Lvl;
  readonly cod: Lvl;
  readonly ren: IntMap<Lvl>;
}
const PRen = (dom: Lvl, cod: Lvl, ren: IntMap<Lvl>): PartialRenaming =>
  ({ dom, cod, ren });

const lift = (pren: PartialRenaming): PartialRenaming =>
  PRen(pren.dom + 1, pren.cod + 1, insert(pren.ren, pren.cod, pren.dom));

const invertSpine = (sp: Spine): [Lvl, IntMap<Lvl>] =>
  sp.foldr((app, [dom, ren]) => {
    if (app.tag !== 'EApp') return terr(`not a variable in the spine: ${app.tag === 'EPrim' ? app.name : app.tag}`);
    const v = force(app.arg);
    if (!isVVar(v)) return terr(`not a variable in the spine`);
    const x = v.head.level;
    if (typeof ren[x] === 'number') return terr(`non-linear spine`);
    return [dom + 1, insert(ren, x, dom)];
  }, [0, {} as IntMap<Lvl>]);

const invert = (gamma: Lvl, sp: Spine): PartialRenaming => {
  const [dom, ren] = invertSpine(sp);
  return PRen(dom, gamma, ren);
};

const renameElim = (id: MetaVar, pren: PartialRenaming, t: Core, e: Elim): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, rename(id, pren, e.arg));
  if (e.tag === 'EProj') return C.Proj(t, e.proj);
  if (e.tag === 'EPrim') return App(e.args.reduce((x, [m, v]) => App(x, m, rename(id, pren, v)), Prim(e.name) as Core), Expl, t);
  return e;
};
const renameSpine = (id: MetaVar, pren: PartialRenaming, t: Core, sp: Spine): Core =>
  sp.foldr((app, fn) => renameElim(id, pren, fn, app), t);

const rename = (id: MetaVar, pren: PartialRenaming, v_: Val): Core => {
  const v = force(v_, false);
  if (v.tag === 'VNatLit') return C.NatLit(v.value);
  if (v.tag === 'VFinLit') return C.FinLit(v.value, rename(id, pren, v.diff), rename(id, pren, v.type));
  if (v.tag === 'VFlex') {
    if (v.head === id) return terr(`occurs check failed: ${id}`);
    return renameSpine(id, pren, Meta(v.head), v.spine);
  }
  if (v.tag === 'VRigid') {
    if (v.head.tag === 'HPrim') return renameSpine(id, pren, Prim(v.head.name), v.spine);
    const x = pren.ren[v.head.level];
    if (typeof x !== 'number') return terr(`escaping variable '${v.head.level}`);
    return renameSpine(id, pren, Var(pren.dom - x - 1), v.spine);
  }
  if (v.tag === 'VGlobal') {
    if (v.head.tag === 'HLVar') return rename(id, pren, v.val.get());
    return renameSpine(id, pren, Global(v.head.name), v.spine); // TODO: should global be forced?
  }
  if (v.tag === 'VAbs')
    return Abs(v.erased, v.mode, v.name, rename(id, pren, v.type), rename(id, lift(pren), vinst(v, VVar(pren.cod))));
  if (v.tag === 'VPi')
    return Pi(v.erased, v.mode, v.name, rename(id, pren, v.type), rename(id, lift(pren), vinst(v, VVar(pren.cod))));
  if (v.tag === 'VSigma')
    return Sigma(v.erased, v.name, rename(id, pren, v.type), rename(id, lift(pren), vinst(v, VVar(pren.cod))));
  if (v.tag === 'VPair') return Pair(rename(id, pren, v.fst), rename(id, pren, v.snd), rename(id, pren, v.type));
  return v;
};

const lams = (lvl: Lvl, a_: Val, t: Core, k: Lvl = 0): Core => {
  if (lvl === k) return t;
  const a = force(a_);
  if (a.tag !== 'VPi') return impossible(`lams, not a pi type: ${a.tag}`);
  const x = a.name === '_' ? `x${k}` : a.name;
  return Abs(a.erased, a.mode, x, quote(a.type, k), lams(lvl, vinst(a, VVar(k)), t, k + 1));
};

const solve = (gamma: Lvl, m: MetaVar, sp: Spine, rhs_: Val): void => {
  log(() => `solve ?${m}${sp.reverse().toString(v => v.tag === 'EApp' ? `${v.mode.tag === 'Expl' ? '' : '{'}${show(v.arg, gamma)}${v.mode.tag === 'Expl' ? '' : '}'}` : v.tag === 'EPrim' ? v.name : v.tag)} := ${show(rhs_, gamma)}`);
  
  // special case for S (?0 ...) ~ v
  if (sp.isCons() && sp.head.tag === 'EPrim' && sp.head.name === 'S') {
    if (rhs_.tag === 'VNatLit' && rhs_.value > 0n)
      return solve(gamma, m, sp.tail, VNatLit(rhs_.value - 1n));
    if (rhs_.tag === 'VRigid' && rhs_.spine.isCons() && rhs_.spine.head.tag === 'EPrim' && rhs_.spine.head.name === 'S')
      return solve(gamma, m, sp.tail, VRigid(rhs_.head, rhs_.spine.tail));
    if (rhs_.tag === 'VFlex' && rhs_.spine.isCons() && rhs_.spine.head.tag === 'EPrim' && rhs_.spine.head.name === 'S')
      return solve(gamma, m, sp.tail, VFlex(rhs_.head, rhs_.spine.tail));
    if (rhs_.tag === 'VGlobal' && rhs_.spine.isCons() && rhs_.spine.head.tag === 'EPrim' && rhs_.spine.head.name === 'S')
      return solve(gamma, m, sp, rhs_.val.get());
  }

  // special case for FS (?0 ...) ~ v
  if (sp.isCons() && sp.head.tag === 'EPrim' && sp.head.name === 'FS') {
    if (rhs_.tag === 'VFinLit' && rhs_.value > 0n)
      return solve(gamma, m, sp.tail, VFinLit(rhs_.value - 1n, rhs_.diff, vpred(rhs_.type)));
    if (rhs_.tag === 'VRigid' && rhs_.spine.isCons() && rhs_.spine.head.tag === 'EPrim' && rhs_.spine.head.name === 'FS')
      return solve(gamma, m, sp.tail, VRigid(rhs_.head, rhs_.spine.tail));
    if (rhs_.tag === 'VFlex' && rhs_.spine.isCons() && rhs_.spine.head.tag === 'EPrim' && rhs_.spine.head.name === 'FS')
      return solve(gamma, m, sp.tail, VFlex(rhs_.head, rhs_.spine.tail));
    if (rhs_.tag === 'VGlobal' && rhs_.spine.isCons() && rhs_.spine.head.tag === 'EPrim' && rhs_.spine.head.name === 'FS')
      return solve(gamma, m, sp, rhs_.val.get());
  }

  const pren = invert(gamma, sp);
  const rhs = rename(m, pren, rhs_);
  const sol = getMeta(m);
  if (sol.tag !== 'Unsolved') return impossible(`solved meta ?${m} in solve`);
  const solutionq = lams(pren.dom, sol.type, rhs);
  log(() => `solution: ${C.show(solutionq)}`);
  if (config.verifyMetaSolutions) {
    const mtype = verify(solutionq, sol.erased ? Local.empty().inType() : Local.empty());
    log(() => `meta verified: ${C.show(mtype)}`);
  }
  const solution = evaluate(solutionq, nil);
  setMeta(m, solution);
};

const unifyPIndex = (k: Lvl, va: Val, vb: Val, sa: Spine, sb: Spine, index: Ix): void => {
  if (index === 0) return unifySpines(k, va, vb, sa, sb);
  if (sa.isCons() && sa.head.tag === 'EProj' && sa.head.proj.tag === 'PProj' && sa.head.proj.proj === 'snd')
    return unifyPIndex(k, va, vb, sa.tail, sb, index - 1);
  return terr(`unify failed (${k}): ${show(va, k)} ~ ${show(vb, k)}`);
};
const unifySpines = (l: Lvl, va: Val, vb: Val, sa: Spine, sb: Spine): void => {
  if (sa.isNil() && sb.isNil()) return;
  if (sa.isCons() && sb.isCons()) {
    const a = sa.head;
    const b = sb.head;
    if (a === b) return unifySpines(l, va, vb, sa.tail, sb.tail);
    if (a.tag === 'EApp' && b.tag === 'EApp' && eqMode(a.mode, b.mode)) {
      unify(l, a.arg, b.arg);
      return unifySpines(l, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EPrim' && b.tag === 'EPrim' && a.name === b.name && a.args.length === b.args.length) {
      for (let i = 0, l = a.args.length; i < l; i++) {
        if (!eqMode(a.args[i][0], b.args[i][0])) return terr(`plicity mismatch in prim elim: ${show(va, l)} ~ ${show(vb, l)}`);
        unify(l, a.args[i][1], b.args[i][1]);
      }
      return unifySpines(l, va, vb, sa.tail, sb.tail);
    }
    if (a.tag === 'EProj' && b.tag === 'EProj') {
      if (a.proj === b.proj)
        return unifySpines(l, va, vb, sa.tail, sb.tail);
      if (a.proj.tag === 'PProj' && b.proj.tag === 'PProj' && a.proj.proj === b.proj.proj)
        return unifySpines(l, va, vb, sa.tail, sb.tail);
      if (a.proj.tag === 'PIndex' && b.proj.tag === 'PIndex' && a.proj.index === b.proj.index)
        return unifySpines(l, va, vb, sa.tail, sb.tail);
      if (a.proj.tag === 'PProj' && a.proj.proj === 'fst' && b.proj.tag === 'PIndex')
        return unifyPIndex(l, va, vb, sa.tail, sb.tail, b.proj.index);
      if (b.proj.tag === 'PProj' && b.proj.proj === 'fst' && a.proj.tag === 'PIndex')
        return unifyPIndex(l, va, vb, sb.tail, sa.tail, a.proj.index);
    }
  }
  return terr(`failed to unify: ${show(va, l)} ~ ${show(vb, l)}`);
};

export const eqHead = (a: Head | GHead, b: Head | GHead): boolean => {
  if (a === b) return true;
  if (a.tag === 'HVar') return b.tag === 'HVar' && a.level === b.level;
  if (a.tag === 'HLVar') return b.tag === 'HLVar' && a.level === b.level;
  if (a.tag === 'HPrim') return b.tag === 'HPrim' && a.name === b.name;
  if (a.tag === 'HGlobal') return b.tag === 'HGlobal' && a.name === b.name;
  return a;
};

export const unify = (l: Lvl, a_: Val, b_: Val): void => {
  const a = force(a_, false);
  const b = force(b_, false);
  log(() => `unify ${show(a, l)} ~ ${show(b, l)}`);
  if (a === b) return;
  if (a.tag === 'VNatLit' && b.tag === 'VNatLit' && a.value === b.value) return;
  if (a.tag === 'VFinLit' && b.tag === 'VFinLit' && a.value === b.value) return;
  if (a.tag === 'VAbs' && b.tag === 'VAbs') {
    const v = VVar(l);
    return unify(l + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VAbs') {
    const v = VVar(l);
    return unify(l + 1, vinst(a, v), vapp(b, a.mode, v));
  }
  if (b.tag === 'VAbs') {
    const v = VVar(l);
    return unify(l + 1, vapp(a, b.mode, v), vinst(b, v));
  }
  if (a.tag === 'VPi' && b.tag === 'VPi' && a.erased === b.erased && eqMode(a.mode, b.mode)) {
    unify(l, a.type, b.type);
    const v = VVar(l);
    return unify(l + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VSigma' && b.tag === 'VSigma' && a.erased === b.erased) {
    unify(l, a.type, b.type);
    const v = VVar(l);
    return unify(l + 1, vinst(a, v), vinst(b, v));
  }
  if (a.tag === 'VPair' && b.tag === 'VPair') {
    unify(l, a.fst, b.fst);
    unify(l, a.snd, b.snd);
    return;
  }
  if (a.tag === 'VPair') {
    unify(l, a.fst, vproj(b, PFst));
    unify(l, a.snd, vproj(b, PSnd));
    return;
  }
  if (b.tag === 'VPair') {
    unify(l, vproj(a, PFst), b.fst);
    unify(l, vproj(a, PSnd), b.snd);
    return;
  }

  if (primEta(a) || primEta(b)) return;
  if (a.tag === 'VFinLit' && a.value === 0n) {
    const ty = force(a.type);
    if (ty.tag === 'VNatLit' && ty.value === 0n) return;
  }
  if (b.tag === 'VFinLit' && b.value === 0n) {
    const ty = force(b.type);
    if (ty.tag === 'VNatLit' && ty.value === 0n) return;
  }

  if (a.tag === 'VRigid' && b.tag === 'VRigid' && eqHead(a.head, b.head))
    return tryT(() => unifySpines(l, a, b, a.spine, b.spine), e => terr(`failed to unify: ${show(a, l)} ~ ${show(b, l)}: ${e}`));
  if (a.tag === 'VFlex' && b.tag === 'VFlex' && a.head === b.head)
    return tryT(() => unifySpines(l, a, b, a.spine, b.spine), e => terr(`failed to unify: ${show(a, l)} ~ ${show(b, l)}: ${e}`));
  if (a.tag === 'VFlex') return solve(l, a.head, a.spine, b);
  if (b.tag === 'VFlex') return solve(l, b.head, b.spine, a);

  if (a.tag === 'VGlobal' && b.tag === 'VGlobal' && eqHead(a.head, b.head) && (config.localGlue || a.head.tag !== 'HLVar'))
    return tryT(() => unifySpines(l, a, b, a.spine, b.spine), () => unify(l, a.val.get(), b.val.get()));
  if (a.tag === 'VGlobal') return unify(l, a.val.get(), b);
  if (b.tag === 'VGlobal') return unify(l, a, b.val.get());

  return terr(`failed to unify: ${show(a, l)} ~ ${show(b, l)}`);
};

const primEta = (a: Val): boolean => {
  const pa = getVPrim(a);
  if (pa) {
    const [x] = pa;
    if (x === '[]') return true;
  }
  return false;
};

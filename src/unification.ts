import { config, log } from './config';
import { Abs, App, Core, Meta, Pi, Var, Global, Sigma, Pair, PFst, PSnd, Prim, Pruning, RevPruning } from './core';
import { freshMeta, getMeta, MetaVar, setMeta } from './metas';
import { Ix, Lvl } from './names';
import { cons, List, nil } from './utils/List';
import { impossible, terr, tryT, tryTE } from './utils/utils';
import { force, isVVar, Spine, vinst, VVar, Val, evaluate, vapp, show, Elim, vproj, Head, GHead, getVPrim, quote, VFlex } from './values';
import * as C from './core';
import { eqMode, Expl, Mode } from './mode';
import { verify } from './verification';
import { Local } from './local';

type IntMap<T> = { [key: number]: T };
const insert = <T>(map: IntMap<T>, key: number, value: T): IntMap<T> =>
  ({ ...map, [key]: value });
const deleteKey = <T>(map: IntMap<T>, key: number): IntMap<T> => {
  const n: IntMap<T> = {};
  for (let k in map) {
    if (+k !== key) n[k] = map[k];
  }
  return n;
};

interface PartialRenaming {
  readonly occ: MetaVar | -1;
  readonly dom: Lvl;
  readonly cod: Lvl;
  readonly ren: IntMap<Lvl>;
}
const PRen = (occ: MetaVar | -1, dom: Lvl, cod: Lvl, ren: IntMap<Lvl>): PartialRenaming =>
  ({ occ, dom, cod, ren });

const lift = (pren: PartialRenaming): PartialRenaming =>
  PRen(pren.occ, pren.dom + 1, pren.cod + 1, insert(pren.ren, pren.cod, pren.dom));

const skip = (pren: PartialRenaming): PartialRenaming =>
  PRen(pren.occ, pren.dom, pren.cod + 1, pren.ren);

const invertSpine = (sp: Spine): [Lvl, IntMap<Lvl>, Pruning, boolean] =>
  sp.foldr((app, [dom, ren, pr, isLinear]) => {
    if (app.tag !== 'EApp') return terr(`not a variable in the spine: ${app.tag === 'EPrim' ? app.name : app.tag}`);
    const v = force(app.arg);
    if (!isVVar(v)) return terr(`not a variable in the spine`);
    const x = v.head.level;
    return typeof ren[x] === 'number' ?
      [dom + 1, deleteKey(ren, x), cons([app.mode, false], pr), false] :
      [dom + 1, insert(ren, x, dom), cons([app.mode, true], pr), isLinear];
  }, [0, {} as IntMap<Lvl>, nil as Pruning, true as boolean]);

const invert = (gamma: Lvl, sp: Spine): [PartialRenaming, Pruning | null] => {
  const [dom, ren, pr, isLinear] = invertSpine(sp);
  return [PRen(-1, dom, gamma, ren), isLinear ? pr : null];
};

const pruneTy = (pr: RevPruning, a_: Val, pren: PartialRenaming = PRen(-1, 0, 0, {})): Core => {
  const a = force(a_);
  if (pr.isNil()) return rename(pren, a);
  if (pr.isCons() && a.tag === 'VPi') {
    if (pr.head[1])
      return Pi(a.erased, a.mode, a.name, rename(pren, a.type),
        pruneTy(pr.tail, vinst(a, VVar(pren.cod)), lift(pren)));
    else
      return pruneTy(pr.tail, vinst(a, VVar(pren.cod)), skip(pren));
  }
  return impossible(`pruneTy, not a pi: ${a.tag}`);
};

const pruneMeta = (pr: Pruning, m: MetaVar): [MetaVar, Val] => {
  const entry = getMeta(m);
  if (entry.tag === 'Solved') return impossible(`pruneMeta, meta is solved: ?${m}`);
  const mty = entry.type;
  const prunedTy = evaluate(pruneTy(pr.reverse(), mty), nil);
  const m2 = freshMeta(prunedTy, entry.erased);
  const solution = lams(pr.length(), mty, C.InsertedMeta(m2, pr));
  const vsolution = evaluate(solution, nil);
  setMeta(m, vsolution);
  return [m2, prunedTy];
};

type SpinePruneStatus = 'OKRenaming' | 'OKNonRenaming' | 'NeedsPruning';

const pruneVFlexSpine = (pren: PartialRenaming, spine: Spine): [List<[Core | null, Mode]>, SpinePruneStatus] =>
  spine.foldr((app, [sp, status]) => {
    if (app.tag !== 'EApp') return terr(`not a variable in the spine: ${app.tag === 'EPrim' ? app.name : app.tag}`);
    const v = force(app.arg);
    if (isVVar(v)) {
      const y = pren.ren[v.head.level];
      const contained = typeof y === 'number';
      if (contained) return [cons([Var(pren.dom - (y + 1)), app.mode], sp), status];
      if (status === 'OKNonRenaming')
        return terr(`pruneVFlexSpine: failed to prune spine (1)`);
      return [cons([null, app.mode], sp), 'NeedsPruning'];
    } else {
      if (status === 'NeedsPruning')
        return terr(`pruneVFlexSpine: failed to prune spine (2)`);
      const t = rename(pren, v);
      return [cons([t, app.mode], sp), 'OKNonRenaming'];
    }
  }, [nil as List<[Core | null, Mode]>, 'OKRenaming' as SpinePruneStatus]);

const pruneVFlex = (pren: PartialRenaming, m: MetaVar, sp_: Spine): [Core, MetaVar, Val] => {
  const [sp, status] = pruneVFlexSpine(pren, sp_);
  let m2, mty;
  if (status === 'NeedsPruning')
    [m2, mty] = pruneMeta(sp.map(([t, i]) => [i, t !== null]), m);
  else {
    const entry = getMeta(m);
    if (entry.tag === 'Solved') return impossible(`pruneVFlex, solved meta: ?${m}`);
    [m2, mty] = [m, entry.type];
  }
  const t = sp.foldr(([mu, i], t) => mu ? App(t, i, mu): t, Meta(m2) as Core);
  return [t, m2, mty];
};

const renameElim = (pren: PartialRenaming, t: Core, e: Elim): Core => {
  if (e.tag === 'EApp') return App(t, e.mode, rename(pren, e.arg));
  if (e.tag === 'EProj') return C.Proj(t, e.proj);
  if (e.tag === 'EPrim') return App(e.args.reduce((x, [m, v]) => App(x, m, rename(pren, v)), Prim(e.name) as Core), Expl, t);
  return e;
};
const renameSpine = (pren: PartialRenaming, t: Core, sp: Spine): Core =>
  sp.foldr((app, fn) => renameElim(pren, fn, app), t);

const rename = (pren: PartialRenaming, v_: Val): Core => {
  const v = force(v_, false);
  if (v.tag === 'VSymbolLit') return C.SymbolLit(v.name);
  if (v.tag === 'VRigid') {
    if (v.head.tag === 'HPrim') return renameSpine(pren, Prim(v.head.name), v.spine);
    const x = pren.ren[v.head.level];
    if (typeof x !== 'number') return terr(`escaping variable '${v.head.level}`);
    return renameSpine(pren, Var(pren.dom - x - 1), v.spine);
  }
  if (v.tag === 'VGlobal') {
    if (v.head.tag === 'HLVar') return rename(pren, v.val.get());
    return renameSpine(pren, Global(v.head.name), v.spine); // TODO: should global be forced?
  }
  if (v.tag === 'VAbs')
    return Abs(v.erased, v.mode, v.name, rename(pren, v.type), rename(lift(pren), vinst(v, VVar(pren.cod))));
  if (v.tag === 'VPi')
    return Pi(v.erased, v.mode, v.name, rename(pren, v.type), rename(lift(pren), vinst(v, VVar(pren.cod))));
  if (v.tag === 'VSigma')
    return Sigma(v.erased, v.name, rename(pren, v.type), rename(lift(pren), vinst(v, VVar(pren.cod))));
  if (v.tag === 'VPair') return Pair(rename(pren, v.fst), rename(pren, v.snd), rename(pren, v.type));
  if (v.tag === 'VFlex') {
    const [m2, sp] = [v.head, v.spine];
    if (pren.occ === -1 || pren.occ !== m2) {
      const [t] = pruneVFlex(pren, m2, sp);
      return t;
    }
    return terr(`occurs check failed: ${m2}`);
  }  
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
  const pren = invert(gamma, sp);
  return solveWithPRen(gamma, m, pren, rhs_);
};

const solveWithPRen = (gamma: Lvl, m: MetaVar, [pren, pruneNonlinear]: [PartialRenaming, Pruning | null], rhs_: Val): void => {
  log(() => `solveWithPRen ?${m} ${pruneNonlinear ? '(pruneNonlinear)' : ''}`);
  const entry = getMeta(m);
  if (entry.tag === 'Solved') return impossible(`solveWithPRen, solved meta: ?${m}`);
  const mty = entry.type;
  log(() => `meta type: ${show(mty, gamma)}`);
  if (pruneNonlinear) pruneTy(pruneNonlinear.reverse(), mty);
  const rhs = rename(PRen(m, pren.dom, pren.cod, pren.ren), rhs_);
  const solutionq = lams(pren.dom, mty, rhs);
  log(() => `solution: ${C.show(solutionq)}`);
  if (config.verifyMetaSolutions) {
    const mtype = verify(solutionq, entry.erased ? Local.empty().inType() : Local.empty());
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

const flexFlex = (l: Lvl, m: MetaVar, sp: Spine, m2: MetaVar, sp2: Spine): void => {
  if (sp.length() < sp2.length()) return flexFlex(l, m2, sp2, m, sp);
  const res = tryTE(() => invert(l, sp));
  if (res instanceof TypeError) {
    const pren = invert(l, sp2);
    return solveWithPRen(l, m2, pren, VFlex(m, sp));
  } else return solveWithPRen(l, m, res, VFlex(m2, sp2));
};

const intersectPruning = (sp: Spine, sp2: Spine): Pruning | null => {
  if (sp.isNil() && sp2.isNil()) return nil;
  if (sp.isCons() && sp2.isCons()) {
    const app = sp.head;
    const app2 = sp2.head;
    if (app.tag !== 'EApp' || app2.tag !== 'EApp' || !eqMode(app.mode, app2.mode))
      return null;
    const v = force(app.arg);
    const v2 = force(app2.arg);
    if (isVVar(v) && isVVar(v2)) {
      const prev = intersectPruning(sp.tail, sp2.tail);
      return prev && cons([app.mode, v.head.level === v2.head.level], prev);
    }
    return null;
  }
  return impossible(`intersectPruning`);
};
const intersect = (l: Lvl, m: MetaVar, sp: Spine, sp2: Spine, va: Val, vb: Val): void => {
  const pr = intersectPruning(sp, sp2);
  if (pr) pruneMeta(pr, m);
  else unifySpines(l, va, vb, sp, sp2);
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
  if (a.tag === 'VSymbolLit' && b.tag === 'VSymbolLit' && a.name === b.name) return;
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
  if (a.tag === 'VPair' && b.tag !== 'VFlex') {
    unify(l, a.fst, vproj(b, PFst));
    unify(l, a.snd, vproj(b, PSnd));
    return;
  }
  if (b.tag === 'VPair' && a.tag !== 'VFlex') {
    unify(l, vproj(a, PFst), b.fst);
    unify(l, vproj(a, PSnd), b.snd);
    return;
  }

  if (primEta(a) || primEta(b)) return;

  if (a.tag === 'VRigid' && b.tag === 'VRigid' && eqHead(a.head, b.head))
    return tryT(() => unifySpines(l, a, b, a.spine, b.spine), e => terr(`failed to unify: ${show(a, l)} ~ ${show(b, l)}: ${e}`));
  if (a.tag === 'VFlex' && b.tag === 'VFlex')
    return a.head === b.head ?
      tryT(() => intersect(l, a.head, a.spine, b.spine, a, b), e => terr(`failed to unify: ${show(a, l)} ~ ${show(b, l)}: ${e}`)) :
      tryT(() => flexFlex(l, a.head, a.spine, b.head, b.spine), e => terr(`failed to unify: ${show(a, l)} ~ ${show(b, l)}: ${e}`));
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

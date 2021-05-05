import { Abs, App, Core, Global, InsertedMeta, Let, Pair, Pi, Sigma, Var, Proj, PIndex, PFst, PSnd, Prim } from './core';
import { indexEnvT, Local, Path } from './local';
import { allMetasSolved, freshMeta, resetMetas, getMeta, getUnsolvedMetas } from './metas';
import { show, Surface } from './surface';
import { cons, List, nil } from './utils/List';
import { evaluate, force, isVUnitType, quote, vadd, Val, VFlex, vinst, VNat, VPi, vproj, VS, VType, VVar, zonk } from './values';
import * as S from './surface';
import * as C from './core';
import { config, log } from './config';
import { impossible, terr, tryT } from './utils/utils';
import { unify } from './unification';
import { Ix, Name } from './names';
import { loadGlobal } from './globals';
import { eqMode, Erasure, Expl, Impl, Mode } from './mode';
import { isPrimErased, isPrimName, primType } from './prims';

export type HoleInfo = [Val, Val, Local, boolean];

const showV = (local: Local, val: Val): string => S.showVal(val, local.level, false, local.ns);

const closeTy = (path: Path, ty: Core): Core =>
  path.foldl((rest, [e, m, x, ty, val]) => val ? Let(e, x, ty, val, rest) : Pi(e, m, x, ty, rest), ty);

const newMeta = (local: Local, ty: Val, erased: Erasure = false): Core => {
  if (isVUnitType(force(ty))) {
    log(() => `short circuit meta with unit type`);
    return C.Unit;
  }
  const qtype = closeTy(local.path, quote(ty, local.level));
  const type = evaluate(qtype, nil);
  const id = freshMeta(type, erased || local.erased); // is this erasure correct?
  log(() => `newMeta ?${id} : ${showV(Local.empty(), type)}`);
  const bds = local.ts.map(e => [e.mode, e.bound] as [Mode, boolean]);
  const meta = InsertedMeta(id, bds);
  return meta;
};

const inst = (local: Local, ty_: Val): [Val, List<Core>] => {
  const ty = force(ty_);
  if (ty.tag === 'VPi' && ty.mode.tag === 'Impl') {
    const m = newMeta(local, ty.type, ty.erased);
    const vm = evaluate(m, local.vs);
    const [res, args] = inst(local, vinst(ty, vm));
    return [res, cons(m, args)];
  }
  return [ty_, nil];
};

const check = (local: Local, tm: Surface, ty: Val): Core => {
  log(() => `check ${show(tm)} : ${showV(local, ty)}${config.showEnvs ? ` in ${local.toString()}` : ''}`);
  if (tm.tag === 'Hole') {
    const x = newMeta(local, ty);
    if (tm.name) {
      if (holes[tm.name]) return terr(`duplicate hole ${tm.name}`);
      holes[tm.name] = [evaluate(x, local.vs), ty, local];
    }
    return x;
  }
  const fty = force(ty);
  log(() => `check(full) ${show(tm)} : ${showV(local, fty)}`);
  if (tm.tag === 'Abs' && !tm.type && fty.tag === 'VPi' && eqMode(tm.mode, fty.mode)) {
    const v = VVar(local.level);
    const x = tm.name;
    const body = check(local.bind(fty.erased, fty.mode, x, fty.type), tm.body, vinst(fty, v));
    return Abs(fty.erased, fty.mode, x, quote(fty.type, local.level), body);
  }
  if (fty.tag === 'VPi' && fty.mode.tag === 'Impl' && tm.tag !== 'Rigid') {
    const v = VVar(local.level);
    const term = check(local.insert(true, fty.mode, fty.name, fty.type), tm, vinst(fty, v));
    return Abs(fty.erased, fty.mode, fty.name, quote(fty.type, local.level), term);
  }
  if (tm.tag === 'Pair' && fty.tag === 'VSigma') {
    const fst = check(fty.erased ? local.inType() : local, tm.fst, fty.type);
    const snd = check(local, tm.snd, vinst(fty, evaluate(fst, local.vs)));
    const qty = quote(ty, local.level);
    log(() => `quoted sigma type (${show(tm)}): ${C.show(qty)}`);
    return Pair(fst, snd, qty);
  }
  if (tm.tag === 'NatLit' && fty.tag === 'VRigid' && fty.head.tag === 'HPrim' && fty.head.name === 'Fin') {
    const m = evaluate(newMeta(local, VNat, true), local.vs);
    const n = vadd(VS(m), tm.value);
    return tryT(() => {
      unify(local.level, n, (fty.spine as any).head.arg);
      return C.FinLit(tm.value, quote(m, local.level), quote(vadd(m, tm.value), local.level));
    }, e => terr(`check failed (${show(tm)} : ${showV(local, fty)}): ${showV(local, n)} ~ ${showV(local, (fty.spine as any).head.arg)}: ${e}`));
  }
  if (tm.tag === 'Let') {
    let vtype: Core;
    let vty: Val;
    let val: Core;
    if (tm.type) {
      vtype = check(local.inType(), tm.type, VType);
      vty = evaluate(vtype, local.vs);
      val = check(tm.erased ? local.inType() : local, tm.val, ty);
    } else {
      [val, vty] = synth(tm.erased ? local.inType() : local, tm.val);
      vtype = quote(vty, local.level);
    }
    const v = evaluate(val, local.vs);
    const body = check(local.define(tm.erased, tm.name, vty, v, vtype, val), tm.body, ty);
    return Let(tm.erased, tm.name, vtype, val, body);
  }
  const [term, ty2] = synth(local, tm.tag === 'Rigid' ? tm.term : tm);
  const [ty2inst, ms] = tm.tag === 'Rigid' ? [ty2, nil] : inst(local, ty2);
  return tryT(() => {
    log(() => `unify ${showV(local, ty2inst)} ~ ${showV(local, ty)}`);
    log(() => `for check ${show(tm)} : ${showV(local, ty)}`);
    unify(local.level, ty2inst, ty);
    return ms.foldl((a, m) => App(a, Impl, m), term);
  }, e => terr(`check failed (${show(tm)}): ${showV(local, ty2)} ~ ${showV(local, ty)}: ${e}`));
};

const freshPi = (local: Local, erased: Erasure, mode: Mode, x: Name): Val => {
  const a = newMeta(local, VType, true);
  const va = evaluate(a, local.vs);
  const b = newMeta(local.bind(erased, mode, '_', va), VType, true);
  return evaluate(Pi(erased, mode, x, a, b), local.vs);
};

const synth = (local: Local, tm: Surface): [Core, Val] => {
  log(() => `synth ${show(tm)}${config.showEnvs ? ` in ${local.toString()}` : ''}`);
  if (tm.tag === 'NatLit') return [C.NatLit(tm.value), VNat];
  if (tm.tag === 'Var') {
    if (isPrimName(tm.name)) {
      if (isPrimErased(tm.name) && !local.erased) return terr(`erased prim used: ${show(tm)}`);
      return [Prim(tm.name), primType(tm.name)];
    } else {
      const i = local.nsSurface.indexOf(tm.name);
      if (i < 0) {
        const entry = loadGlobal(tm.name);
        if (!entry) return terr(`global ${tm.name} not found`);
        if (entry.erased && !local.erased) return terr(`erased global used: ${show(tm)}`);
        return [Global(tm.name), entry.type];
      } else {
        const [entry, j] = indexEnvT(local.ts, i) || terr(`var out of scope ${show(tm)}`);
        log(() => `local: ${i} ~> ${j}`);
        if (entry.erased && !local.erased) return terr(`erased var used: ${show(tm)}`);
        return [Var(j), entry.type];
      }
    }
  }
  if (tm.tag === 'App') {
    const [fn, fnty] = synth(local, tm.fn);
    const [arg, rty, ms] = synthapp(local, fnty, tm.mode, tm.arg, tm);
    return [App(ms.foldl((a, m) => App(a, Impl, m), fn), tm.mode, arg), rty];
  }
  if (tm.tag === 'Abs') {
    if (tm.type) {
      const type = check(local.inType(), tm.type, VType);
      const ty = evaluate(type, local.vs);
      const [body, rty] = synth(local.bind(tm.erased, tm.mode, tm.name, ty), tm.body);
      const qpi = Pi(tm.erased, tm.mode, tm.name, type, quote(rty, local.level + 1));
      const pi = evaluate(qpi, local.vs);
      return [Abs(tm.erased, tm.mode, tm.name, type, body), pi];
    } else {
      const pi = freshPi(local, tm.erased, tm.mode, tm.name);
      const term = check(local, tm, pi);
      return [term, pi];
    }
  }
  if (tm.tag === 'Pi') {
    if (!local.erased) return terr(`pi type in non-type context: ${show(tm)}`);
    const type = check(local.inType(), tm.type, VType);
    const ty = evaluate(type, local.vs);
    const body = check(local.inType().bind(tm.erased, tm.mode, tm.name, ty), tm.body, VType);
    const pi = Pi(tm.erased, tm.mode, tm.name, type, body);
    return [pi, VType];
  }
  if (tm.tag === 'Sigma') {
    if (!local.erased) return terr(`sigma type in non-type context: ${show(tm)}`);
    const type = check(local.inType(), tm.type, VType);
    const ty = evaluate(type, local.vs);
    const body = check(local.inType().bind(tm.erased, Expl, tm.name, ty), tm.body, VType);
    return [Sigma(tm.erased, tm.name, type, body), VType];
  }
  if (tm.tag === 'Proj') {
    const [term, sigma_] = synth(local, tm.term);
    if (tm.proj.tag === 'PProj') {
      const sigma = force(sigma_);
      if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showV(local, sigma_)}`);
      if (sigma.erased && tm.proj.proj === 'fst' && !local.erased)
        return terr(`cannot project erased ${show(tm)}: ${showV(local, sigma_)}`);
      const fst = sigma.name !== '_'  ? PIndex(sigma.name, 0) : PFst; // TODO: is this nice?
      return [Proj(term, tm.proj), tm.proj.proj === 'fst' ? sigma.type : vinst(sigma, vproj(evaluate(term, local.vs), fst))];
    } else if (tm.proj.tag === 'PName') {
      const orig = evaluate(term, local.vs);
      const [ty, ix] = projectName(local, tm, orig, orig, sigma_, tm.proj.name, 0);
      return [Proj(term, PIndex(tm.proj.name, ix)), ty];
    } else return [Proj(term, PIndex(null, tm.proj.index)), projectIndex(local, tm, evaluate(term, local.vs), sigma_, tm.proj.index)];
  }
  if (tm.tag === 'Let') {
    let type: Core;
    let ty: Val;
    let val: Core;
    if (tm.type) {
      type = check(local.inType(), tm.type, VType);
      ty = evaluate(type, local.vs);
      val = check(tm.erased ? local.inType() : local, tm.val, ty);
    } else {
      [val, ty] = synth(tm.erased ? local.inType() : local, tm.val);
      type = quote(ty, local.level);
    }
    const v = evaluate(val, local.vs);
    const [body, rty] = synth(local.define(tm.erased, tm.name, ty, v, type, val), tm.body);
    return [Let(tm.erased, tm.name, type, val, body), rty];
  }
  if (tm.tag === 'Hole') {
    const vt = evaluate(newMeta(local, VType, true), local.vs);
    const t = newMeta(local, vt);
    if (tm.name) {
      if (holes[tm.name]) return terr(`duplicate hole ${tm.name}`);
      holes[tm.name] = [evaluate(t, local.vs), vt, local];
    }
    return [t, vt];
  }
  if (tm.tag === 'Pair') {
    let erased = false;
    if (tm.fst.tag === 'Var') {
      const i = local.nsSurface.indexOf(tm.fst.name);
      if (i >= 0) {
        const res = indexEnvT(local.ts, i);
        if (res) {
          erased = res[0].erased;
        }
      }
    }
    const [fst, fstty] = synth(erased ? local.inType() : local, tm.fst);
    const [snd, sndty] = synth(local, tm.snd);
    const ty = Sigma(erased, tm.fst.tag === 'Var' ? tm.fst.name : '_', quote(fstty, local.level), quote(sndty, local.level + 1));
    return [Pair(fst, snd, ty), evaluate(ty, local.vs)];
  }
  if (tm.tag === 'Ann') {
    const type = check(local.inType(), tm.type, VType);
    log(() => `eval type in Ann`);
    const vtype = evaluate(type, local.vs);
    const term = check(local, tm.term, vtype);
    return [Let(false, 'x', type, term, Var(0)), vtype];
  }
  if (tm.tag === 'Import') {
    const [term, sigma_] = synth(local, tm.term);
    const vterm = evaluate(term, local.vs);
    return createImportTerm(local, term, vterm, sigma_, tm.imports, tm.body);
  }
  if (tm.tag === 'Rigid') return terr(`can only use rigid in checking position: ${show(tm)}`);
  return terr(`unable to synth ${show(tm)}`);
};

const createImportTerm = (local: Local, term: Core, vterm: Val, sigma_: Val, imports: string[] | null, body: Surface, i: Ix = 0): [Core, Val] => {
  log(() => `createImportTerm (${local.level}) ${S.showCore(term, local.ns)} ${showV(local, sigma_)}`);
  const sigma = force(sigma_);
  if (sigma.tag === 'VSigma') {
    let name = sigma.name;
    let nextimports = imports;
    let found = false;
    if (imports) {
      const nameix = imports.indexOf(sigma.name);
      if (nameix < 0) {
        name = '_';
      } else {
        nextimports = imports.slice(0);
        nextimports.splice(nameix, 1);      
        found = true;
      }
    } else {
      found = true;
    }
    if (found) {
      const val = vproj(vterm, PIndex(sigma.name, i));
      const qtype = quote(sigma.type, local.level);
      const newlocal = local.define(sigma.erased, name, sigma.type, val, qtype, quote(val, local.level));
      const val2 = evaluate(Var(0), newlocal.vs);
      const [rest, ty] = createImportTerm(newlocal, term, vterm, vinst(sigma, val2), nextimports, body, i + 1);
      return [Let(sigma.erased, name, qtype, Proj(term, PIndex(sigma.name, i)), rest), ty];
    } else {
      return createImportTerm(local, term, vterm, vinst(sigma, vproj(vterm, PIndex(sigma.name, i))), nextimports, body, i + 1);
    }
  }
  if (imports && imports.length > 0) return terr(`failed to import, names not in module: ${imports.join(' ')}`);
  log(() => `names in import body scope: ${local.ns}`);
  return synth(local, body);
};

const projectIndex = (local: Local, full: Surface, tm: Val, ty_: Val, index: Ix): Val => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (ty.erased && index === 0 && !local.erased)
        return terr(`cannot project erased ${show(full)}: ${showV(local, ty)}`);
    if (index === 0) return ty.type;
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    return projectIndex(local, full, vproj(tm, PSnd), vinst(ty, vproj(tm, fst)), index - 1);
  }
  return terr(`failed to project, ${show(full)}: ${showV(local, ty_)}`);
};
const projectName = (local: Local, full: Surface, orig: Val, tm: Val, ty_: Val, x: Name, ix: Ix, ns: List<Name> = nil): [Val, Ix] => {
  log(() => `projectName (${showV(local, tm)}) (${showV(local, ty_)}) ${x} ${ix} ${ns.toString()}`);
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (ty.erased && ty.name === x && !local.erased)
        return terr(`cannot project erased ${show(full)}: ${showV(local, ty)}`);
    if (ty.name === x) return [ty.type, ix];
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    const vfst = ty.name !== '_' ? (!ns.contains(ty.name) ? vproj(orig, PIndex(ty.name, ix)) : vproj(tm, PIndex(ty.name, 0))) : vproj(tm, fst);
    log(() => showV(local, vfst));
    return projectName(local, full, orig, vproj(tm, PSnd), vinst(ty, vfst), x, ix + 1, cons(ty.name, ns));
  }
  return terr(`failed to project, ${show(full)}: ${showV(local, ty_)}`);
};

const synthapp = (local: Local, ty_: Val, mode: Mode, tm: Surface, tmall: Surface): [Core, Val, List<Core>] => {
  log(() => `synthapp ${showV(local, ty_)} @ ${mode.tag === 'Expl' ? '' : '{'}${show(tm)}${mode.tag === 'Expl' ? '' : '}'}${config.showEnvs ? ` in ${local.toString()}` : ''}`);
  const ty = force(ty_);
  if (ty.tag === 'VPi' && ty.mode.tag === 'Impl' && mode.tag === 'Expl') {
    const m = newMeta(local, ty.type, ty.erased);
    const vm = evaluate(m, local.vs);
    const [rest, rt, l] = synthapp(local, vinst(ty, vm), mode, tm, tmall);
    return [rest, rt, cons(m, l)];
  }
  if (ty.tag === 'VPi' && eqMode(ty.mode, mode)) {
    const right = check(ty.erased ? local.inType() : local, tm, ty.type);
    const rt = vinst(ty, evaluate(right, local.vs));
    return [right, rt, nil];
  }
  if (ty.tag === 'VFlex') {
    const m = getMeta(ty.head);
    if (m.tag !== 'Unsolved') return impossible(`solved meta ?${ty.head} in synthapp`);
    const a = freshMeta(m.type, m.erased);
    const b = freshMeta(m.type, m.erased);
    const pi = VPi(false, mode, '_', VFlex(a, ty.spine), () => VFlex(b, ty.spine));
    unify(local.level, ty, pi);
    return synthapp(local, pi, mode, tm, tmall);
  }
  return terr(`invalid type or plicity mismatch in synthapp in ${show(tmall)}: ${showV(local, ty)} @ ${mode.tag === 'Expl' ? '' : '{'}${show(tm)}${mode.tag === 'Expl' ? '' : '}'}`);
};

type Holes = { [key: string]: [Val, Val, Local] }
let holes: Holes = {};

const showValSZ = (local: Local, v: Val) =>
  S.showCore(zonk(quote(v, local.level, false), local.vs, local.level, false), local.ns);
const showHoles = (tm: Core, ty: Core) => {
  const holeprops = Object.entries(holes);
  if (holeprops.length === 0) return;
  const strtype = S.showCore(ty);
  const strterm = S.showCore(tm);
  const str = holeprops.map(([x, [t, v, local]]) => {
    const fst = local.ns.zipWith(local.vs, (x, v) => [x, v] as [Name, Val]);
    const all = fst.zipWith(local.ts, ([x, v], { bound: def, type: ty, inserted, erased }) => [x, v, def, ty, inserted, erased] as [Name, Val, boolean, Val, boolean, boolean]);
    const allstr = all.toMappedArray(([x, v, b, t, _, p]) => `${p ? `{${x}}` : x} : ${showValSZ(local, t)}${b ? '' : ` = ${showValSZ(local, v)}`}`).join('\n');
    return `\n_${x} : ${showValSZ(local, v)} = ${showValSZ(local, t)}\nlocal:\n${allstr}\n`;
  }).join('\n');
  return terr(`unsolved holes\ntype: ${strtype}\nterm: ${strterm}\n${str}`);
};

const showUnsolvedMetas = (local: Local): string =>
  getUnsolvedMetas().map(m => `${m.erased ? '-' : ''}?${m.id} : ${showV(local, m.type)}`).join('\n');

export const elaborate = (t: Surface, local: Local = Local.empty()): [Core, Core] => {
  holes = {};
  resetMetas();
  const [tm, ty] = synth(local, t);
  const qty = quote(ty, local.level);

  log(() => C.show(qty));
  log(() => C.show(tm));

  log(() => S.showCore(qty, local.ns));
  log(() => S.showCore(tm, local.ns));

  const zty = zonk(qty, local.vs, local.level);
  log(() => S.showCore(zty, local.ns));
  const ztm = zonk(tm, local.vs, local.level);
  log(() => S.showCore(ztm, local.ns));

  showHoles(ztm, zty);

  if (!allMetasSolved())
    return terr(`not all metas are solved: ${S.showCore(ztm, local.ns)} : ${S.showCore(zty, local.ns)}\n\n${showUnsolvedMetas(local)}`);
  return [ztm, zty];
};

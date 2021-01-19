import { log } from './config';
import { conv } from './conversion';
import { Core, PFst, Pi, PIndex, PSnd, show } from './core';
import { Erased } from './erased';
import { globalLoad } from './globals';
import { indexEnvT, Local, showVal, showValCore } from './local';
import { eqMode, Expl, Mode } from './mode';
import { Ix } from './names';
import { synthPrim, synthPrimElim } from './prims';
import { addUses, lubUses, lubUsesAll, many, multiplyUses, noUses, one, sub, Usage, Uses, zero } from './usage';
import { terr, tryT } from './utils/utils';
import { evaluate, force, quote, Val, vinst, vproj, VPropEq, VType } from './values';
import * as E from './erased';

const check = (local: Local, tm: Core, ty: Val): [Uses, Erased] => {
  log(() => `check ${show(tm)} : ${showValCore(local, ty)}`);
  const [ty2, u, er] = synth(local, tm);
  return tryT(() => {
    log(() => `unify ${showValCore(local, ty2)} ~ ${showValCore(local, ty)}`);
    conv(local.level, ty2, ty);
    return [u, er];
  }, e => terr(`check failed (${show(tm)}): ${showValCore(local, ty2)} ~ ${showValCore(local, ty)}: ${e}`));
};

const synth = (local: Local, tm: Core): [Val, Uses, Erased] => {
  log(() => `synth ${show(tm)}`);
  if (tm.tag === 'Prim') return [synthPrim(tm.name), noUses(local.level), E.erasePrim(tm.name)];
  if (tm.tag === 'Var') {
    const [entry, j, erasedNo] = indexEnvT(local.ts, tm.index) || terr(`var out of scope ${show(tm)}`);
    const uses = noUses(local.level).updateAt(j, _ => local.usage);
    return [entry.type, uses, E.Var(tm.index - erasedNo)];
  }
  if (tm.tag === 'Global') {
    const e = globalLoad(tm.name);
    if (!e) return terr(`undefined global or failed to load global ${tm.name}`);
    return [e.type, noUses(local.level), E.Global(tm.name)];
  }
  if (tm.tag === 'App') {
    const [fnty, fnu, fner] = synth(local, tm.fn);
    const [rty, argu, arger, u] = synthapp(local, fnty, tm.mode, tm.arg);
    return [rty, addUses(fnu, argu), u === zero ? fner: E.App(fner, arger)];
  }
  if (tm.tag === 'Abs') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [rty, u, erbody] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
    const pi = evaluate(Pi(tm.usage, tm.mode, tm.name, tm.type, quote(rty, local.level + 1)), local.vs);
    const [ux, urest] = u.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [pi, urest, tm.usage === zero ? erbody : E.Abs(erbody)];
  }
  if (tm.tag === 'Pi') {
    const [u1] = check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [u2] = check(local.bind(many, tm.mode, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [VType, addUses(u1, urest), E.Type];
  }
  if (tm.tag === 'Let') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [uv, erval] = check(tm.usage === zero ? local.inType() : local, tm.val, ty);
    const v = evaluate(tm.val, local.vs);
    const [rty, ub, erbody] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
    const [ux, urest] = ub.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [rty, addUses(multiplyUses(ux, uv), urest), tm.usage === zero ? erbody : E.Let(erval, erbody)];
  }
  if (tm.tag === 'Sigma') {
    const [u1] = check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [u2] = check(local.bind(many, Expl, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [VType, addUses(u1, urest), E.Type];
  }
  if (tm.tag === 'Pair') {
    check(local.inType(), tm.type, VType);
    const vsigma_ = evaluate(tm.type, local.vs);
    const vsigma = force(vsigma_);
    if (vsigma.tag !== 'VSigma') return terr(`pair without sigma type: ${show(tm)}`);
    const [u1, erfst] = check(local, tm.fst, vsigma.type);
    const [u2, ersnd] = check(local, tm.snd, vinst(vsigma, evaluate(tm.fst, local.vs)));
    if (vsigma.exclusive)
      return [vsigma_, lubUses(u1, u2), E.Pair(erfst, ersnd)]; // TODO: do I need to use the sigma usage?
    return [vsigma_, addUses(multiplyUses(vsigma.usage, u1), u2), vsigma.usage === zero ? ersnd : E.Pair(erfst, ersnd)];
  }
  if (tm.tag === 'PrimElim') {
    if (!sub(one, tm.usage))
      return terr(`usage must be 1 <= q in ${show(tm)} but got ${tm.usage}`);
    const [ty_, u1, erscrut] = synth(local, tm.scrut);
    const [amount, cont] = synthPrimElim(tm.name);
    if (tm.cases.length !== amount)
      return terr(`invalid case amount, expected ${amount} but got ${tm.cases.length} in ${show(tm)}`);
    try {
      const [tmotive, contcases] = cont(ty_, tm.usage);
      check(local.inType(), tm.motive, tmotive);
      const vmotive = evaluate(tm.motive, local.vs);
      const vscrut = evaluate(tm.scrut, local.vs);
      const [tycases, rty] = contcases(vmotive, vscrut);
      if (tycases.length !== amount) return terr(`invalid ${tm.name}: amount does not match`);
      const usesAndEr = tycases.map((ty, i) => check(local, tm.cases[i], ty));
      const uses = usesAndEr.map(x => x[0]);
      const ercases = usesAndEr.map(x => x[1]);
      const scrutu = multiplyUses(tm.usage, u1);
      return [rty, uses.length === 0 ? scrutu : addUses(scrutu, lubUsesAll(uses)), E.erasePrimElim(tm.name, erscrut, ercases)];
    } catch (err) {
      if (!(err instanceof TypeError)) throw err;
      return terr(`synth ${show(tm)} failed: ${err}`);
    }
  }
  if (tm.tag === 'Proj') {
    const [sigma_, u, erterm] = synth(local, tm.term);
    if (tm.proj.tag === 'PProj') {
      const sigma = force(sigma_);
      if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showVal(local, sigma_)}`);
      if (local.usage === one && (sigma.usage === one || (sigma.usage === zero && tm.proj.proj === 'fst')))
        return terr(`cannot project ${show(tm)}, usage must be * or 0 with a second projection: ${showVal(local, sigma_)}`);
      const fst = sigma.name !== '_'  ? PIndex(sigma.name, 0) : PFst; // TODO: is this nice?
      return [tm.proj.proj === 'fst' ? sigma.type : vinst(sigma, vproj(evaluate(tm.term, local.vs), fst)), u, sigma.usage === zero ? erterm : E.Proj(erterm, tm.proj.proj === 'fst' ? E.PFst : E.PSnd)];
    } else {
      const [ty, erindex] = project(local, tm, evaluate(tm.term, local.vs), sigma_, tm.proj.index, 0);
      return [ty, u, E.Proj(erterm, E.PIndex(erindex))];
    }
  }
  if (tm.tag === 'PropEq') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [u1] = check(local, tm.left, ty);
    const [u2] = check(local, tm.right, ty);
    return [VType, addUses(u1, u2), E.Type];
  }
  if (tm.tag === 'Refl') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    check(local.inType(), tm.val, ty);
    const x = evaluate(tm.val, local.vs);
    return [VPropEq(ty, x, x), noUses(local.level), E.False];
  }
  return tm;
};

const project = (local: Local, full: Core, tm: Val, ty_: Val, index: Ix, erindex: Ix): [Val, Ix] => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (local.usage === one && (ty.usage === one || (ty.usage === zero && index === 0)))
      return terr(`cannot project ${show(full)}, usage must be * or 0 with a second projection: ${showVal(local, ty_)}`);
    if (index === 0) return [ty.type, erindex];
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    return project(local, full, vproj(tm, PSnd), vinst(ty, vproj(tm, fst)), index - 1, ty.usage === zero ? erindex : erindex + 1);
  }
  return terr(`failed to project, ${show(full)}: ${showVal(local, ty_)}`);
};

const synthapp = (local: Local, ty_: Val, mode: Mode, arg: Core): [Val, Uses, Erased, Usage] => {
  log(() => `synthapp ${showValCore(local, ty_)} @ ${show(arg)}`);
  const ty = force(ty_);
  if (ty.tag === 'VPi' && eqMode(ty.mode, mode)) {
    const cty = ty.type;
    const [uses, er] = check(local, arg, cty);
    const v = evaluate(arg, local.vs);
    return [vinst(ty, v), multiplyUses(ty.usage, uses), er, ty.usage];
  }
  return terr(`not a correct pi type in synthapp: ${showValCore(local, ty)} @ ${show(arg)}`);
};

export const typecheck = (t: Core, local: Local = Local.empty()): [Core, Erased] => {
  const [vty, , er] = synth(local, t);
  const ty = quote(vty, local.level);
  return [ty, er];
};

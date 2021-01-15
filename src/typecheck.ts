import { log } from './config';
import { conv } from './conversion';
import { Core, PFst, Pi, PIndex, PSnd, show } from './core';
import { globalLoad } from './globals';
import { indexEnvT, Local, showVal, showValCore } from './local';
import { eqMode, Expl, Mode } from './mode';
import { Ix } from './names';
import { synthPrim, synthPrimElim } from './prims';
import { addUses, lubUses, lubUsesAll, many, multiplyUses, noUses, one, sub, Uses, zero } from './usage';
import { terr, tryT } from './utils/utils';
import { evaluate, force, quote, Val, vinst, vproj, VPropEq, VType } from './values';

const check = (local: Local, tm: Core, ty: Val): Uses => {
  log(() => `check ${show(tm)} : ${showValCore(local, ty)}`);
  const [ty2, u] = synth(local, tm);
  return tryT(() => {
    log(() => `unify ${showValCore(local, ty2)} ~ ${showValCore(local, ty)}`);
    conv(local.level, ty2, ty);
    return u;
  }, e => terr(`check failed (${show(tm)}): ${showValCore(local, ty2)} ~ ${showValCore(local, ty)}: ${e}`));
};

const synth = (local: Local, tm: Core): [Val, Uses] => {
  log(() => `synth ${show(tm)}`);
  if (tm.tag === 'Prim') return [synthPrim(tm.name), noUses(local.level)];
  if (tm.tag === 'Var') {
    const [entry, j] = indexEnvT(local.ts, tm.index) || terr(`var out of scope ${show(tm)}`);
    const uses = noUses(local.level).updateAt(j, _ => local.usage);
    return [entry.type, uses];
  }
  if (tm.tag === 'Global') {
    const e = globalLoad(tm.name);
    if (!e) return terr(`undefined global or failed to load global ${tm.name}`);
    return [e.type, noUses(local.level)];
  }
  if (tm.tag === 'App') {
    const [fnty, fnu] = synth(local, tm.fn);
    const [rty, argu] = synthapp(local, fnty, tm.mode, tm.arg);
    return [rty, addUses(fnu, argu)];
  }
  if (tm.tag === 'Abs') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [rty, u] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
    const pi = evaluate(Pi(tm.usage, tm.mode, tm.name, tm.type, quote(rty, local.level + 1)), local.vs);
    const [ux, urest] = u.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [pi, urest];
  }
  if (tm.tag === 'Pi') {
    const u1 = check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const u2 = check(local.bind(many, tm.mode, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [VType, addUses(u1, urest)];
  }
  if (tm.tag === 'Let') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const uv = check(tm.usage === zero ? local.inType() : local, tm.val, ty);
    const v = evaluate(tm.val, local.vs);
    const [rty, ub] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
    const [ux, urest] = ub.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [rty, addUses(multiplyUses(ux, uv), urest)];
  }
  if (tm.tag === 'Sigma') {
    const u1 = check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const u2 = check(local.bind(many, Expl, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [VType, addUses(u1, urest)];
  }
  if (tm.tag === 'Pair') {
    check(local.inType(), tm.type, VType);
    const vsigma_ = evaluate(tm.type, local.vs);
    const vsigma = force(vsigma_);
    if (vsigma.tag !== 'VSigma') return terr(`pair without sigma type: ${show(tm)}`);
    const u1 = check(local, tm.fst, vsigma.type);
    const u2 = check(local, tm.snd, vinst(vsigma, evaluate(tm.fst, local.vs)));
    if (vsigma.exclusive)
      return [vsigma_, lubUses(u1, u2)]; // TODO: do I need to use the sigma usage?
    return [vsigma_, addUses(multiplyUses(vsigma.usage, u1), u2)];
  }
  if (tm.tag === 'PrimElim') {
    if (!sub(one, tm.usage))
      return terr(`usage must be 1 <= q in ${show(tm)} but got ${tm.usage}`);
    const [ty_, u1] = synth(local, tm.scrut);
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
      const uses = tycases.map((ty, i) => check(local, tm.cases[i], ty));
      const scrutu = multiplyUses(tm.usage, u1);
      return [rty, uses.length === 0 ? scrutu : addUses(scrutu, lubUsesAll(uses))];
    } catch (err) {
      if (!(err instanceof TypeError)) throw err;
      return terr(`synth ${show(tm)} failed: ${err}`);
    }
  }
  if (tm.tag === 'Proj') {
    const [sigma_, u] = synth(local, tm.term);
    if (tm.proj.tag === 'PProj') {
      const sigma = force(sigma_);
      if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showVal(local, sigma_)}`);
      if (local.usage === one && (sigma.usage === one || (sigma.usage === zero && tm.proj.proj === 'fst')))
        return terr(`cannot project ${show(tm)}, usage must be * or 0 with a second projection: ${showVal(local, sigma_)}`);
      const fst = sigma.name !== '_'  ? PIndex(sigma.name, 0) : PFst; // TODO: is this nice?
      return [tm.proj.proj === 'fst' ? sigma.type : vinst(sigma, vproj(evaluate(tm.term, local.vs), fst)), u];
    } else return [project(local, tm, evaluate(tm.term, local.vs), sigma_, tm.proj.index), u];
  }
  if (tm.tag === 'PropEq') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const u1 = check(local, tm.left, ty);
    const u2 = check(local, tm.right, ty);
    return [VType, addUses(u1, u2)];
  }
  if (tm.tag === 'Refl') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    check(local.inType(), tm.val, ty);
    const x = evaluate(tm.val, local.vs);
    return [VPropEq(ty, x, x), noUses(local.level)];
  }
  return tm;
};

const project = (local: Local, full: Core, tm: Val, ty_: Val, index: Ix): Val => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (local.usage === one && (ty.usage === one || (ty.usage === zero && index === 0)))
      return terr(`cannot project ${show(full)}, usage must be * or 0 with a second projection: ${showVal(local, ty_)}`);
    if (index === 0) return ty.type;
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    return project(local, full, vproj(tm, PSnd), vinst(ty, vproj(tm, fst)), index - 1);
  }
  return terr(`failed to project, ${show(full)}: ${showVal(local, ty_)}`);
};

const synthapp = (local: Local, ty_: Val, mode: Mode, arg: Core): [Val, Uses] => {
  log(() => `synthapp ${showValCore(local, ty_)} @ ${show(arg)}`);
  const ty = force(ty_);
  if (ty.tag === 'VPi' && eqMode(ty.mode, mode)) {
    const cty = ty.type;
    const uses = check(local, arg, cty);
    const v = evaluate(arg, local.vs);
    return [vinst(ty, v), multiplyUses(ty.usage, uses)];
  }
  return terr(`not a correct pi type in synthapp: ${showValCore(local, ty)} @ ${show(arg)}`);
};

export const typecheck = (t: Core, local: Local = Local.empty()): Core => {
  const [vty] = synth(local, t);
  const ty = quote(vty, local.level);
  return ty;
};

import { log } from './config';
import { Core, PFst, Pi, PIndex, PSnd, show } from './core';
import { loadGlobal } from './globals';
import { indexEnvT, Local } from './local';
import { impossible, terr, tryT } from './utils/utils';
import { evaluate, force, quote, Val, vinst, VType } from './values';
import * as V from './values';
import { unify } from './unification';
import { eqMode, Expl, Mode } from './mode';
import { isPrimErased, primType } from './prims';
import { Ix } from './names';

const showV = (local: Local, v: Val) => V.show(v, local.level);

const check = (local: Local, tm: Core, ty: Val): void => {
  log(() => `check ${show(tm)} : ${showV(local, ty)}`);
  const ty2 = synth(local, tm);
  return tryT(() => {
    log(() => `unify ${showV(local, ty2)} ~ ${showV(local, ty)}`);
    unify(local.level, ty2, ty);
    return;
  }, e => terr(`check failed (${show(tm)}): ${showV(local, ty2)} ~ ${showV(local, ty)}: ${e}`));
};

const synth = (local: Local, tm: Core): Val => {
  log(() => `synth ${show(tm)}`);
  if (tm.tag === 'Meta' || tm.tag === 'InsertedMeta') return impossible(`${tm.tag} in typecheck`);
  if (tm.tag === 'Var') {
    const [entry] = indexEnvT(local.ts, tm.index) || terr(`var out of scope ${show(tm)}`);
    if (entry.erased && !local.erased) return terr(`erased var used: ${show(tm)}`);
    return entry.type;
  }
  if (tm.tag === 'Prim') {
    if (isPrimErased(tm.name) && !local.erased) return terr(`erased prim used: ${show(tm)}`);
    return primType(tm.name);
  }
  if (tm.tag === 'Global') {
    const e = loadGlobal(tm.name);
    if (!e) return terr(`undefined global ${show(tm)}`);
    if (e.erased && !local.erased) return terr(`erased global used: ${show(tm)}`);
    return e.type;
  }
  if (tm.tag === 'App') {
    const fnty = synth(local, tm.fn);
    const rty = synthapp(local, fnty, tm.mode, tm.arg);
    return rty;
  }
  if (tm.tag === 'Abs') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const rty = synth(local.bind(tm.erased, tm.mode, tm.name, ty), tm.body);
    const qpi = Pi(tm.erased, tm.mode, tm.name, tm.type, quote(rty, local.level + 1));
    const pi = evaluate(qpi, local.vs);
    return pi;
  }
  if (tm.tag === 'Pair') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const fty = force(ty);
    if (fty.tag !== 'VSigma') return terr(`not a sigma type in pair (${show(tm)}): ${showV(local, ty)}`);
    check(fty.erased ? local.inType() : local, tm.fst, fty.type);
    check(local, tm.snd, vinst(fty, evaluate(tm.fst, local.vs)));
    return ty;
  }
  if (tm.tag === 'Pi') {
    if (!local.erased) return terr(`pi type in non-type context: ${show(tm)}`);
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    check(local.inType().bind(tm.erased, tm.mode, tm.name, ty), tm.body, VType);
    return VType;
  }
  if (tm.tag === 'Sigma') {
    if (!local.erased) return terr(`sigma type in non-type context: ${show(tm)}`);
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    check(local.inType().bind(tm.erased, Expl, tm.name, ty), tm.body, VType);
    return VType;
  }
  if (tm.tag === 'Let') {
    check(local.inType(), tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    check(tm.erased ? local.inType() : local, tm.val, ty);
    const v = evaluate(tm.val, local.vs);
    const rty = synth(local.define(tm.erased, tm.name, ty, v), tm.body);
    return rty;
  }
  if (tm.tag === 'Proj') {
    const sigma_ = synth(local, tm.term);
    if (tm.proj.tag === 'PProj') {
      const sigma = force(sigma_);
      if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showV(local, sigma_)}`);
      if (sigma.erased && tm.proj.proj === 'fst' && !local.erased)
        return terr(`cannot project erased ${show(tm)}: ${showV(local, sigma_)}`);
      const fst = sigma.name !== '_'  ? PIndex(sigma.name, 0) : PFst; // TODO: is this nice?
      return tm.proj.proj === 'fst' ? sigma.type : vinst(sigma, V.vproj(evaluate(tm.term, local.vs), fst));
    } else return project(local, tm, evaluate(tm.term, local.vs), sigma_, tm.proj.index);
  }
  return tm;
};

const project = (local: Local, full: Core, tm: Val, ty_: Val, index: Ix): Val => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
      if (ty.erased && index === 0 && !local.erased)
      return terr(`cannot project erased sigma (${show(full)}): ${showV(local, ty_)}`);
    if (index === 0) return ty.type;
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    return project(local, full, V.vproj(tm, PSnd), vinst(ty, V.vproj(tm, fst)), index - 1);
  }
  return terr(`failed to project, ${show(full)}: ${showV(local, ty_)}`);
};

const synthapp = (local: Local, ty_: Val, mode: Mode, arg: Core): Val => {
  log(() => `synthapp ${showV(local, ty_)} @ ${mode.tag === 'Expl' ? '' : '{'}${show(arg)}${mode.tag === 'Expl' ? '' : ''}`);
  const ty = force(ty_);
  if (ty.tag === 'VPi' && eqMode(ty.mode, mode)) {
    check(ty.erased ? local.inType() : local, arg, ty.type);
    const v = evaluate(arg, local.vs);
    return vinst(ty, v);
  }
  return terr(`not a correct pi type or mode mismatch in synthapp: ${showV(local, ty)} @ ${mode.tag === 'Expl' ? '' : '{'}${show(arg)}${mode.tag === 'Expl' ? '' : ''}`);
};

export const verify = (t: Core, local: Local = Local.empty()): Core => {
  const vty = synth(local, t);
  const ty = quote(vty, local.level);
  return ty;
};

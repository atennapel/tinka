import { log } from './config';
import { Abs, App, Let, Pi, Core, Type, Var, Pair, Sigma } from './core';
import { terr, tryT } from './utils/utils';
import { evaluate, quote, Val, vinst, VSigma, VType, VVar } from './values';
import { Surface } from './surface';
import { show } from './surface';
import { conv } from './conversion';
import { addUses, many, multiplyUses, noUses, one, sub, Uses } from './usage';
import { indexEnvT, Local, showVal } from './local';
import { eqMode, Expl, Mode } from './mode';

const check = (local: Local, tm: Surface, ty: Val): [Core, Uses] => {
  log(() => `check (${local.level}) ${show(tm)} : ${showVal(local, ty)}`);
  if (tm.tag === 'Type' && ty.tag === 'VType') return [Type, noUses(local.level)];
  if (tm.tag === 'Abs' && !tm.type && ty.tag === 'VPi' && eqMode(tm.mode, ty.mode)) {
    const v = VVar(local.level);
    const x = tm.name;
    const [body, u] = check(local.bind(ty.usage, ty.mode, x, ty.type), tm.body, vinst(ty, v));
    const [ux, urest] = u.uncons();
    if (!sub(ux, ty.usage))
      return terr(`usage error in ${show(tm)}: expected ${ty.usage} for ${x} but actual ${ux}`);
    return [Abs(ty.usage, ty.mode, x, quote(ty.type, local.level), body), urest];
  }
  /*
  if (ty.tag === 'VPi' && ty.mode.tag === 'Impl' && !(tm.tag === 'Abs' && tm.mode.tag === 'Impl')) {
    const v = VVar(local.level);
    const x = ty.name;
    const [term, u] = check(local.insert(ty.usage, ty.mode, x, ty.type), tm, vinst(ty, v));
    const [ux, urest] = u.uncons();
    if (!sub(ux, ty.usage))
      return terr(`usage error in ${show(tm)}: expected ${ty.usage} for ${x} but actual ${ux}`);
    return [Abs(ty.usage, ty.mode, x, quote(ty.type, local.level), term), urest];
  }
  */
  if (tm.tag === 'Pair' && ty.tag === 'VSigma') {
    const [fst, u1] = check(local, tm.fst, ty.type);
    const [snd, u2] = check(local, tm.snd, vinst(ty, evaluate(fst, local.vs)));
    return [Pair(fst, snd, quote(ty, local.level)), addUses(multiplyUses(ty.usage, u1), u2)];
  }
  if (tm.tag === 'Let') {
    let vtype: Core;
    let vty: Val;
    let val: Core;
    let uv: Uses;
    if (tm.type) {
      [vtype] = check(local, tm.type, VType);
      vty = evaluate(vtype, local.vs);
      [val, uv] = check(local, tm.val, ty);
    } else {
      [val, vty, uv] = synth(local, tm.val);
      vtype = quote(vty, local.level);
    }
    const v = evaluate(val, local.vs);
    const [body, ub] = check(local.define(tm.usage, tm.name, vty, v), tm.body, ty);
    const [ux, urest] = ub.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [Let(tm.usage, tm.name, vtype, val, body), addUses(multiplyUses(ux, uv), urest)];
  }
  const [Core, ty2, uses] = synth(local, tm);
  return tryT(() => {
    log(() => `unify ${showVal(local, ty2)} ~ ${showVal(local, ty)}`);
    conv(local.level, ty2, ty);
    return [Core, uses];
  }, e => terr(`check failed (${show(tm)}): ${showVal(local, ty2)} ~ ${showVal(local, ty)}: ${e}`));
};

const synth = (local: Local, tm: Surface): [Core, Val, Uses] => {
  log(() => `synth (${local.level}) ${show(tm)}`);
  if (tm.tag === 'Type') return [Type, VType, noUses(local.level)];
  if (tm.tag === 'Var') {
    const i = local.nsSurface.indexOf(tm.name);
    if (i < 0) return terr(`undefined var ${tm.name}`);
    else {
      const [entry, j] = indexEnvT(local.ts, i) || terr(`var out of scope ${show(tm)}`);
      const uses = noUses(local.level).updateAt(j, _ => one);
      return [Var(j), entry.type, uses];
    }
  }
  if (tm.tag === 'App') {
    const [fntm, fnty, fnu] = synth(local, tm.fn);
    const [argtm, rty, fnarg] = synthapp(local, fnty, tm.mode, tm.arg);
    return [App(fntm, tm.mode, argtm), rty, addUses(fnu, fnarg)];
  }
  if (tm.tag === 'Abs') {
    if (tm.type) {
      const [type] = check(local, tm.type, VType);
      const ty = evaluate(type, local.vs);
      const [body, rty, u] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
      const pi = evaluate(Pi(tm.usage, tm.mode, tm.name, type, quote(rty, local.level + 1)), local.vs);
      const [ux, urest] = u.uncons();
      if (!sub(ux, tm.usage))
        return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
      return [Abs(tm.usage, tm.mode, tm.name, type, body), pi, urest];
    } else terr(`cannot synth unannotated lambda: ${show(tm)}`);
  }
  if (tm.tag === 'Pi') {
    const [type, u1] = check(local, tm.type, VType);
    const ty = evaluate(type, local.vs);
    const [body, u2] = check(local.bind(many, tm.mode, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [Pi(tm.usage, tm.mode, tm.name, type, body), VType, addUses(u1, urest)];
  }
  if (tm.tag === 'Let') {
    let type: Core;
    let ty: Val;
    let val: Core;
    let uv: Uses;
    if (tm.type) {
      [type] = check(local, tm.type, VType);
      ty = evaluate(type, local.vs);
      [val, uv] = check(local, tm.val, ty);
    } else {
      [val, ty, uv] = synth(local, tm.val);
      type = quote(ty, local.level);
    }
    const v = evaluate(val, local.vs);
    const [body, rty, ub] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
    const [ux, urest] = ub.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [Let(tm.usage, tm.name, type, val, body), rty, addUses(multiplyUses(ux, uv), urest)];
  }
  if (tm.tag === 'Sigma') {
    const [type, u1] = check(local, tm.type, VType);
    const ty = evaluate(type, local.vs);
    const [body, u2] = check(local.bind(many, Expl, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [Sigma(tm.usage, tm.name, type, body), VType, addUses(u1, urest)];
  }
  if (tm.tag === 'Pair') {
    const [fst, ty1, u1] = synth(local, tm.fst);
    const [snd, ty2, u2] = synth(local, tm.snd);
    const ty = VSigma(many, '_', ty1, _ => ty2);
    return [Pair(fst, snd, quote(ty, local.level)), ty, addUses(multiplyUses(ty.usage, u1), u2)];
  }
  return terr(`unable to synth ${show(tm)}`);
};

const synthapp = (local: Local, ty: Val, mode: Mode, arg: Surface): [Core, Val, Uses] => {
  log(() => `synthapp (${local.level}) ${showVal(local, ty)} @ ${show(arg)}`);
  if (ty.tag === 'VPi' && eqMode(ty.mode, mode)) {
    const cty = ty.type;
    const [Core, uses] = check(local, arg, cty);
    const v = evaluate(Core, local.vs);
    return [Core, vinst(ty, v), multiplyUses(ty.usage, uses)];
  }
  return terr(`not a correct pi type in synthapp: ${showVal(local, ty)} @ ${show(arg)}`);
};

export const elaborate = (t: Surface, local: Local = Local.empty()): [Core, Core] => {
  const [tm, vty] = synth(local, t);
  const ty = quote(vty, 0);
  return [tm, ty];
};

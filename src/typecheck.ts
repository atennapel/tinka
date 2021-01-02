import { log } from './config';
import { conv } from './conversion';
import { Core, Pi, show } from './core';
import { indexEnvT, Local, showValCore } from './local';
import { eqMode, Mode } from './mode';
import { addUses, many, multiplyUses, noUses, one, sub, Uses } from './usage';
import { impossible, terr, tryT } from './utils/utils';
import { evaluate, quote, Val, vinst, VType } from './values';

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
  if (tm.tag === 'Type') return [VType, noUses(local.level)];
  if (tm.tag === 'Var') {
    const [entry, j] = indexEnvT(local.ts, tm.index) || terr(`var out of scope ${show(tm)}`);
    const uses = noUses(local.level).updateAt(j, _ => one);
    return [entry.type, uses];
  }
  if (tm.tag === 'Global') return impossible('Globals are unimplemented'); // TODO
  if (tm.tag === 'App') {
    const [fnty, fnu] = synth(local, tm.fn);
    const [rty, argu] = synthapp(local, fnty, tm.mode, tm.arg);
    return [rty, addUses(fnu, argu)];
  }
  if (tm.tag === 'Abs') {
    check(local, tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const [rty, u] = synth(local.bind(tm.usage, tm.mode, tm.name, ty), tm.body);
    const pi = evaluate(Pi(tm.usage, tm.mode, tm.name, tm.type, quote(rty, local.level + 1)), local.vs);
    const [ux, urest] = u.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [pi, urest];
  }
  if (tm.tag === 'Pi') {
    const u1 = check(local, tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const u2 = check(local.bind(many, tm.mode, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [VType, addUses(u1, urest)];
  }
  if (tm.tag === 'Let') {
    check(local, tm.type, VType);
    const ty = evaluate(tm.type, local.vs);
    const uv = check(local, tm.val, ty);
    const v = evaluate(tm.val, local.vs);
    const [rty, ub] = synth(local.define(tm.usage, tm.name, ty, v), tm.body);
    const [ux, urest] = ub.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [rty, addUses(multiplyUses(ux, uv), urest)];
  }
  return tm;
};

const synthapp = (local: Local, ty: Val, mode: Mode, arg: Core): [Val, Uses] => {
  log(() => `synthapp ${showValCore(local, ty)} @ ${show(arg)}`);
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
  const ty = quote(vty, 0);
  return ty;
};

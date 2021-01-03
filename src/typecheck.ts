import { log } from './config';
import { conv } from './conversion';
import { Core, Pi, show } from './core';
import { indexEnvT, Local, showVal, showValCore } from './local';
import { eqMode, Expl, Mode } from './mode';
import { addUses, many, multiply, multiplyUses, noUses, one, sub, Uses } from './usage';
import { impossible, terr, tryT } from './utils/utils';
import { evaluate, force, quote, Val, vapp, vinst, VPair, VPi, VType } from './values';

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
    const uses = noUses(local.level).updateAt(j, _ => local.usage);
    return [entry.type, uses];
  }
  if (tm.tag === 'Global') return impossible('Globals are unimplemented'); // TODO
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
    const uv = check(local, tm.val, ty);
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
    return [vsigma_, addUses(multiplyUses(vsigma.usage, u1), u2)];
  }
  if (tm.tag === 'IndSigma') {
    /*
      1 <= q
      G |- p : (u x : A) ** B
      G |- P : ((u x : A) ** B x) -> Type
      G |- k : (q * u x : A) -> (q y : B x) -> P (x, y)
      ---------------------------------------------
      q * G |- indSigma q P p k : P p
    */
    if (!sub(one, tm.usage))
      return terr(`usage must be 1 <= q in sigma induction ${show(tm)}: ${tm.usage}`)
    const [sigma_, u1] = synth(local, tm.scrut);
    const sigma = force(sigma_);
    if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showVal(local, sigma_)}`);
    check(local.inType(), tm.motive, VPi(many, Expl, '_', sigma_, _ => VType));
    const motive = evaluate(tm.motive, local.vs);
    const u2 = check(local, tm.cas, VPi(multiply(tm.usage, sigma.usage), Expl, 'x', sigma.type, x => VPi(tm.usage, Expl, 'y', vinst(sigma, x), y => vapp(motive, Expl, VPair(x, y, sigma_)))));
    return [vapp(motive, Expl, evaluate(tm.scrut, local.vs)), multiplyUses(tm.usage, addUses(u1, u2))];
  }
  return tm;
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
  const ty = quote(vty, 0);
  return ty;
};

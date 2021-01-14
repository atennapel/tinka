import { log } from './config';
import { Abs, App, Let, Pi, Core, Var, Pair, Sigma, ElimSigma, Global, Proj, PFst, PIndex, PSnd, subst, shift, PropEq, Refl, ElimPropEq, Prim, ElimBool, UnitType, Unit } from './core';
import { terr, tryT } from './utils/utils';
import { evaluate, force, quote, Val, vapp, VBool, VFalse, vinst, VPair, VPi, vproj, VPropEq, VRefl, VSigma, VTrue, VType, VVar } from './values';
import { Surface, show } from './surface';
import * as S from './surface';
import { conv } from './conversion';
import { addUses, lubUses, many, multiply, multiplyUses, noUses, one, sub, Usage, Uses, zero } from './usage';
import { indexEnvT, Local, showVal } from './local';
import { eqMode, Expl, Impl, Mode } from './mode';
import { globalLoad } from './globals';
import { Ix, Lvl, Name } from './names';
import { List } from './utils/List';
import { isPrimName, synthPrim } from './prims';

const check = (local: Local, tm: Surface, ty_: Val): [Core, Uses] => {
  log(() => `check (${local.level}) ${show(tm)} : ${showVal(local, ty_)}`);
  const ty = force(ty_);
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
    if (ty.exclusive)
      return [Pair(fst, snd, quote(ty, local.level)), lubUses(u1, u2)]; // TODO
    return [Pair(fst, snd, quote(ty, local.level)), addUses(multiplyUses(ty.usage, u1), u2)];
  }
  if (tm.tag === 'Refl' && !tm.type && !tm.val && ty.tag === 'VPropEq') {
    tryT(() => conv(local.level, ty.left, ty.right), e => terr(`check failed (${show(tm)}): ${showVal(local, ty_)}: ${e}`));
    return [Refl(quote(ty.type, local.level), quote(ty.left, local.level)), noUses(local.level)];
  }
  if (tm.tag === 'Let') {
    let vtype: Core;
    let vty: Val;
    let val: Core;
    let uv: Uses;
    if (tm.type) {
      [vtype] = check(local.inType(), tm.type, VType);
      vty = evaluate(vtype, local.vs);
      [val, uv] = check(tm.usage === zero ? local.inType() : local, tm.val, ty);
    } else {
      [val, vty, uv] = synth(tm.usage === zero ? local.inType() : local, tm.val);
      vtype = quote(vty, local.level);
    }
    const v = evaluate(val, local.vs);
    const [body, ub] = check(local.define(tm.usage, tm.name, vty, v), tm.body, ty_);
    const [ux, urest] = ub.uncons();
    if (!sub(ux, tm.usage))
      return terr(`usage error in ${show(tm)}: expected ${tm.usage} for ${tm.name} but actual ${ux}`);
    return [Let(tm.usage, tm.name, vtype, val, body), addUses(multiplyUses(ux, uv), urest)];
  }
  if (tm.tag === 'Hole') {
    const n = local.level;
    const ts = local.ts;
    const ns = local.ns;
    const vs = local.vs;
    const usage = local.usage;
    const r: string[] = [];
    for (let i = 0; i < n; i++) {
      const t = ts.index(i);
      const v = vs.index(i);
      const x = ns.index(i);
      if (!t || !v || !x) continue;
      const type = showVal(local, t.type);
      r.push(`${t.inserted ? 'inserted ' : ''}${t.usage === many ? '' : `${t.usage} `}${eqMode(t.mode, Impl) ? '{' : ''}${x}${eqMode(t.mode, Impl) ? '}' : ''} : ${type}${t.bound ? '' : ` = ${showVal(local, v)}`}`);
    }
    return terr(`hole: ${show(tm)}, expected type: ${showVal(local, ty_)}\nlocal (${usage}):\n${r.join('\n')}`);
  }
  const [Core, ty2, uses] = synth(local, tm);
  return tryT(() => {
    log(() => `unify ${showVal(local, ty2)} ~ ${showVal(local, ty_)}`);
    conv(local.level, ty2, ty_);
    return [Core, uses];
  }, e => terr(`check failed (${show(tm)}): ${showVal(local, ty2)} ~ ${showVal(local, ty_)}: ${e}`));
};

const synth = (local: Local, tm: Surface): [Core, Val, Uses] => {
  log(() => `synth (${local.level}) ${show(tm)}`);
  if (tm.tag === 'Var') {
    if (isPrimName(tm.name)) {
      const p = synthPrim(tm.name);
      if (!p) return terr(`undefined primitive ${show(tm)}`);
      return [Prim(tm.name), p, noUses(local.level)];
    } else {
      const i = local.nsSurface.indexOf(tm.name);
      if (i < 0) {
        const e = globalLoad(tm.name);
        if (e) return [Global(tm.name), e.type, noUses(local.level)];
        return terr(`undefined global ${tm.name}`);
      } else {
        const [entry, j] = indexEnvT(local.ts, i) || terr(`undefined variable ${show(tm)}`);
        const uses = noUses(local.level).updateAt(j, _ => local.usage);
        return [Var(j), entry.type, uses];
      }
    }
  }
  if (tm.tag === 'App') {
    const [fntm, fnty, fnu] = synth(local, tm.fn);
    const [argtm, rty, fnarg] = synthapp(local, fnty, tm.mode, tm.arg);
    return [App(fntm, tm.mode, argtm), rty, addUses(fnu, fnarg)];
  }
  if (tm.tag === 'Abs') {
    if (tm.type) {
      const [type] = check(local.inType(), tm.type, VType);
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
    const [type, u1] = check(local.inType(), tm.type, VType);
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
      [type] = check(local.inType(), tm.type, VType);
      ty = evaluate(type, local.vs);
      [val, uv] = check(tm.usage === zero ? local.inType() : local, tm.val, ty);
    } else {
      [val, ty, uv] = synth(tm.usage === zero ? local.inType() : local, tm.val);
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
    const [type, u1] = check(local.inType(), tm.type, VType);
    const ty = evaluate(type, local.vs);
    const [body, u2] = check(local.bind(many, Expl, tm.name, ty), tm.body, VType);
    const [, urest] = u2.uncons();
    return [Sigma(tm.usage, tm.exclusive, tm.name, type, body), VType, addUses(u1, urest)];
  }
  if (tm.tag === 'Pair') {
    const [fst, ty1, u1] = synth(local, tm.fst);
    const [snd, ty2, u2] = synth(local, tm.snd);
    const ty = VSigma(many, false, '_', ty1, _ => ty2);
    return [Pair(fst, snd, quote(ty, local.level)), ty, addUses(multiplyUses(ty.usage, u1), u2)];
  }
  if (tm.tag === 'ElimSigma') {
    if (!sub(one, tm.usage))
      return terr(`usage must be 1 <= q in sigma induction ${show(tm)}: ${tm.usage}`)
    const [scrut, sigma_, u1] = synth(local, tm.scrut);
    const sigma = force(sigma_);
    if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showVal(local, sigma_)}`);
    if (sigma.exclusive) return terr(`cannot call elimSigma on exclusive sigma in ${show(tm)}: ${showVal(local, sigma_)}`);
    const [motive] = check(local.inType(), tm.motive, VPi(many, Expl, '_', sigma_, _ => VType));
    const vmotive = evaluate(motive, local.vs);
    const [cas, u2] = check(local, tm.cas, VPi(multiply(tm.usage, sigma.usage), Expl, 'x', sigma.type, x => VPi(tm.usage, Expl, 'y', vinst(sigma, x), y => vapp(vmotive, Expl, VPair(x, y, sigma_)))));
    return [ElimSigma(tm.usage, motive, scrut, cas), vapp(vmotive, Expl, evaluate(scrut, local.vs)), multiplyUses(tm.usage, addUses(u1, u2))];
  }
  if (tm.tag === 'ElimPropEq') {
    if (!sub(one, tm.usage))
      return terr(`usage must be 1 <= q in equality induction ${show(tm)}: ${tm.usage}`);
    const [scrut, eq_, u1] = synth(local, tm.scrut);
    const eq = force(eq_);
    if (eq.tag !== 'VPropEq') return terr(`not a equality type in ${show(tm)}: ${showVal(local, eq_)}`);
    const A = eq.type;
    const [motive] = check(local.inType(), tm.motive, VPi(many, Expl, 'x', A, x => VPi(many, Expl, 'y', A, y => VPi(many, Expl, '_', VPropEq(A, x, y), _ => VType))));
    const vmotive = evaluate(motive, local.vs);
    const castype = VPi(zero, Expl, 'x', A, x => vapp(vapp(vapp(vmotive, Expl, x), Expl, x), Expl, VRefl(A, x)));
    const [cas, u2] = check(local, tm.cas, castype);
    const vscrut = evaluate(scrut, local.vs);
    return [ElimPropEq(tm.usage, motive, scrut, cas), vapp(vapp(vapp(vmotive, Expl, eq.left), Expl, eq.right), Expl, vscrut), multiplyUses(tm.usage, addUses(u1, u2))];
  }
  if (tm.tag === 'ElimBool') {
    if (!sub(one, tm.usage))
      return terr(`usage must be 1 <= q in Bool induction ${show(tm)}: ${tm.usage}`);
    const [scrut, u1] = check(local, tm.scrut, VBool);
    const [motive] = check(local.inType(), tm.motive, VPi(many, Expl, '_', VBool, _ => VType));
    const vmotive = evaluate(motive, local.vs);
    const [trueBranch, u2] = check(local, tm.trueBranch, vapp(vmotive, Expl, VTrue));
    const [falseBranch, u3] = check(local, tm.falseBranch, vapp(vmotive, Expl, VFalse));
    const vscrut = evaluate(scrut, local.vs);
    return [ElimBool(tm.usage, motive, scrut, trueBranch, falseBranch), vapp(vmotive, Expl, vscrut), addUses(multiplyUses(tm.usage, u1), lubUses(u2, u3))];
  }
  if (tm.tag === 'Proj') {
    const [term, sigma_, u] = synth(local, tm.term);
    if (tm.proj.tag === 'PProj') {
      const sigma = force(sigma_);
      if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showVal(local, sigma_)}`);
      if (local.usage === one && (sigma.usage === one || (sigma.usage === zero && tm.proj.proj === 'fst')))
        return terr(`cannot project ${show(tm)}, usage must be * or 0 with a second projection: ${showVal(local, sigma_)}`);
      const fst = sigma.name !== '_'  ? PIndex(sigma.name, 0) : PFst; // TODO: is this nice?
      return [Proj(term, tm.proj), tm.proj.proj === 'fst' ? sigma.type : vinst(sigma, vproj(evaluate(term, local.vs), fst)), u];
    } else if (tm.proj.tag === 'PName') {
      const [ty, ix] = projectName(local, tm, evaluate(term, local.vs), sigma_, tm.proj.name, 0);
      return [Proj(term, PIndex(tm.proj.name, ix)), ty, u];
    } else return [Proj(term, PIndex(null, tm.proj.index)), projectIndex(local, tm, evaluate(term, local.vs), sigma_, tm.proj.index), u];
  }
  if (tm.tag === 'Import') {
    const [, sigma_,] = synth(local, tm.term);
    const sigma = force(sigma_);
    if (sigma.tag !== 'VSigma') return terr(`not a sigma type in ${show(tm)}: ${showVal(local, sigma_)}`);
    const [imports, all] = getAllNamesFromSigma(local.level, sigma, tm.imports);
    if (tm.imports) for (const i of tm.imports) if (!all.includes(i))
       return terr(`import includes name not included in module (${i}) in ${show(tm)}: ${showVal(local, sigma_)}`);
    const v = '$import';
    const vv = tm.term.tag === 'Var' ? tm.term : S.Var(v);
    const lets = imports.reduceRight((t, [x, u]) => S.Let(u, x, null, S.Proj(vv, S.PName(x)), t), tm.body);
    const lets2 = tm.term.tag === 'Var' ? lets : S.Let(many, v, null, tm.term, lets);
    return synth(local, lets2); // TODO: improve this elaboration
  }
  if (tm.tag === 'Signature') {
    let clocal = local;
    const edefs: [S.SigEntry, Core][] = [];
    for (let i = 0, l = tm.defs.length; i < l; i++) {
      const e = tm.defs[i];
      let type: Core;
      if (e.type) {
        [type] = check(clocal.inType(), e.type, VType);
      } else {
        // type = newMeta(clocal, e.erased, VType);
        return terr(`signature definition must have a type: ${show(tm)}`);
      }
      edefs.push([e, type]);
      const ty = evaluate(type, clocal.vs);
      clocal = clocal.bind(e.usage, Expl, e.name, ty);
    }
    const stype = edefs.reduceRight((t, [e, type]) => Sigma(e.usage, false, e.name, type, t), UnitType as Core);
    return [stype, VType, noUses(local.level)];
  }
  if (tm.tag === 'Module') {
    const defs = List.from(tm.defs);
    const [term, type, u] = createModuleTerm(local, defs);
    return [term, evaluate(type, local.vs), u];
  }
  if (tm.tag === 'PropEq') {
    if (tm.type) {
      const [type] = check(local.inType(), tm.type, VType);
      const ty = evaluate(type, local.vs);
      const [left, u1] = check(local, tm.left, ty);
      const [right, u2] = check(local, tm.right, ty);
      return [PropEq(type, left, right), VType, addUses(u1, u2)];
    } else {
      const [left, ty, u1] = synth(local, tm.left);
      const [right, u2] = check(local, tm.right, ty);
      return [PropEq(quote(ty, local.level), left, right), VType, addUses(u1, u2)];
    }
  }
  if (tm.tag === 'Refl' && tm.type && tm.val) {
    const [type] = check(local.inType(), tm.type, VType);
    const ty = evaluate(type, local.vs);
    const [val] = check(local.inType(), tm.val, ty);
    const x = evaluate(val, local.vs);
    return [Refl(type, val), VPropEq(ty, x, x), noUses(local.level)];
  }
  return terr(`unable to synth ${show(tm)}`);
};

const createModuleTerm = (local: Local, entries: List<S.ModEntry>): [Core, Core, Uses] => {
  if (entries.isCons()) {
    const e = entries.head;
    const rest = entries.tail;
    let type: Core;
    let ty: Val;
    let val: Core;
    let u: Uses;
    if (e.type) {
      [type] = check(local.inType(), e.type, VType);
      ty = evaluate(type, local.vs);
      [val, u] = check(e.usage === zero ? local.inType() : local, e.val, ty);
    } else {
      [val, ty, u] = synth(e.usage === zero ? local.inType() : local, e.val);
      type = quote(ty, local.level);
    }
    const v = evaluate(val, local.vs);
    const nextlocal = local.define(e.usage, e.name, ty, v);
    const [nextterm, nexttype, u2] = createModuleTerm(nextlocal, rest);
    const nextuses = addUses(multiplyUses(e.usage, u), u2);
    if (e.priv) {
      return [Let(e.usage, e.name, type, val, nextterm), subst(nexttype, val), nextuses];
    } else {
      const sigma = Sigma(e.usage, false, e.name, type, nexttype);
      return [Let(e.usage, e.name, type, val, Pair(Var(0), nextterm, shift(1, 0, sigma))), sigma, nextuses];
    }
  }
  return [Unit, UnitType, noUses(local.level)];
};

const getAllNamesFromSigma = (k: Lvl, ty_: Val, ns: string[] | null, a: [string, Usage][] = [], all: string[] = []): [[string, Usage][], string[]] => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (!ns || ns.includes(ty.name)) a.push([ty.name, ty.usage]);
    all.push(ty.name);
    return getAllNamesFromSigma(k + 1, vinst(ty, VVar(k)), ns, a, all);
  }
  return [a, all];
};

const projectIndex = (local: Local, full: Surface, tm: Val, ty_: Val, index: Ix): Val => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (local.usage === one && (ty.usage === one || (ty.usage === zero && index === 0)))
      return terr(`cannot project ${show(full)}, usage must be * or 0 with a second projection: ${showVal(local, ty_)}`);
    if (index === 0) return ty.type;
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    return projectIndex(local, full, vproj(tm, PSnd), vinst(ty, vproj(tm, fst)), index - 1);
  }
  return terr(`failed to project, ${show(full)}: ${showVal(local, ty_)}`);
};
const projectName = (local: Local, full: Surface, tm: Val, ty_: Val, x: Name, ix: Ix): [Val, Ix] => {
  const ty = force(ty_);
  if (ty.tag === 'VSigma') {
    if (local.usage === one && (ty.usage === one || (ty.usage === zero && ty.name === x)))
      return terr(`cannot project ${show(full)}, usage must be * or 0 with a second projection: ${showVal(local, ty_)}`);
    if (ty.name === x) return [ty.type, ix];
    const fst = ty.name !== '_'  ? PIndex(ty.name, 0) : PFst; // TODO: is this nice?
    return projectName(local, full, vproj(tm, PSnd), vinst(ty, vproj(tm, fst)), x, ix + 1);
  }
  return terr(`failed to project, ${show(full)}: ${showVal(local, ty_)}`);
};

const synthapp = (local: Local, ty_: Val, mode: Mode, arg: Surface): [Core, Val, Uses] => {
  log(() => `synthapp (${local.level}) ${showVal(local, ty_)} @ ${show(arg)}`);
  const ty = force(ty_);
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
  const ty = quote(vty, local.level);
  return [tm, ty];
};

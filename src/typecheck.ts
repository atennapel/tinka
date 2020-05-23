import { Term, Pi, Let, Abs, App, Global, Var, showTerm, isUnsolved, showSurfaceZ, Sort, UnsafeCast, Sigma, Pair, Fst, Snd, Enum, Elem, EnumInd, Desc } from './syntax';
import { EnvV, Val, showTermQ, VType, force, evaluate, extendV, VVar, quote, showEnvV, showTermS, zonk, VPi, VNe, HMeta, forceGlue, VSigma, vfst, VEnum, vapp, VElem } from './domain';
import { Nil, List, Cons, listToString, indexOf, mapIndex, filter, foldr, foldl } from './utils/list';
import { Ix, Name } from './names';
import { terr } from './utils/utils';
import { unify } from './unify';
import { Plicity } from './surface';
import * as S from './surface';
import { log, config } from './config';
import { globalGet, globalSet } from './globalenv';
import { freshMeta, freshMetaId, metaPush, metaDiscard, metaPop } from './metas';
import { verify } from './verify';

type EntryT = { type: Val, bound: boolean, plicity: Plicity, inserted: boolean };
type EnvT = List<EntryT>;
const extendT = (ts: EnvT, val: Val, bound: boolean, plicity: Plicity, inserted: boolean): EnvT =>
  Cons({ type: val, bound, plicity, inserted }, ts);
const showEnvT = (ts: EnvT, k: Ix = 0, full: boolean = false): string =>
  listToString(ts, entry => `${entry.bound ? '' : 'd '}${entry.plicity ? 'e ' : ''}${entry.inserted ? 'i ' : ''}${showTermQ(entry.type, k, full)}`);
const indexT = (ts: EnvT, ix: Ix): [EntryT, Ix] | null => {
  let l = ts;
  let i = 0;
  while (l.tag === 'Cons') {
    if (l.head.inserted) {
      l = l.tail;
      i++;
      continue;
    }
    if (ix === 0) return [l.head, i];
    i++;
    ix--;
    l = l.tail;
  }
  return null;
};

export interface Local {
  names: List<Name>;
  namesSurface: List<Name>;
  ts: EnvT;
  vs: EnvV;
  index: Ix;
  inType: boolean;
}
export const localEmpty: Local = { names: Nil, namesSurface: Nil, ts: Nil, vs: Nil, index: 0, inType: false };
export const extend = (l: Local, name: Name, ty: Val, bound: boolean, plicity: Plicity, inserted: boolean, val: Val, inType: boolean = l.inType): Local => ({
  names: Cons(name, l.names),
  namesSurface: inserted ? l.namesSurface : Cons(name, l.namesSurface),
  ts: extendT(l.ts, ty, bound, plicity, inserted),
  vs: extendV(l.vs, val),
  index: l.index + 1,
  inType,
});
export const localInType = (l: Local, inType: boolean = true): Local => ({
  names: l.names,
  namesSurface: l.namesSurface,
  ts: l.ts,
  vs: l.vs,
  index: l.index,
  inType,
});
export const showLocal = (l: Local, full: boolean = false): string =>
  `Local(${l.index}, ${l.inType}, ${showEnvT(l.ts, l.index, full)}, ${showEnvV(l.vs, l.index, full)}, ${listToString(l.names)}, ${listToString(l.namesSurface)})`;

const newMeta = (ts: EnvT): Term => {
  const spine = filter(mapIndex(ts, (i, { bound }) => bound ? Var(i) : null), x => x !== null) as List<Var>;
  return foldr((x, y) => App(y, false, x), freshMeta() as Term, spine);
};

const inst = (ts: EnvT, vs: EnvV, ty_: Val): [Val, List<Term>] => {
  const ty = forceGlue(ty_);
  if (ty.tag === 'VPi' && ty.plicity) {
    const m = newMeta(ts);
    const vm = evaluate(m, vs);
    const [res, args] = inst(ts, vs, ty.body(vm));
    return [res, Cons(m, args)];
  }
  return [ty, Nil];
};

const check = (local: Local, tm: S.Term, ty: Val): Term => {
  log(() => `check ${S.showTerm(tm)} : ${showTermS(ty, local.names, local.index)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const fty = force(ty);
  if (tm.tag === 'Sort' && fty.tag === 'VSort' && fty.sort === '*') return Sort(tm.sort);
  if (tm.tag === 'Desc' && fty.tag === 'VSort' && fty.sort === '*') return Desc;
  if (tm.tag === 'Enum' && fty.tag === 'VSort' && fty.sort === '*') return Desc;
  if (tm.tag === 'Hole') {
    const x = newMeta(local.ts);
    return x;
  }
  if (tm.tag === 'UnsafeCast') {
    const type = quote(ty, local.index, false);
    const [val] = synth(local, tm.val);
    return UnsafeCast(type, val);
  }
  if (tm.tag === 'Pair' && fty.tag === 'VSigma') {
    const fst = check(local, tm.fst, fty.type);
    const snd = check(local, tm.snd, fty.body(evaluate(fst, local.vs)));
    return Pair(fst, snd, quote(ty, local.index, false));
  }
  if (tm.tag === 'Elem' && tm.total === null && fty.tag === 'VEnum' && tm.num < fty.num)
    return Elem(tm.num, fty.num);
  if (tm.tag === 'Abs' && !tm.type && fty.tag === 'VPi' && tm.plicity === fty.plicity) {
    const v = VVar(local.index);
    const x = tm.name === '_' ? fty.name : tm.name;
    const body = check(extend(local, x, fty.type, true, fty.plicity, false, v), tm.body, fty.body(v));
    return Abs(tm.plicity, x, quote(fty.type, local.index, false), body);
  }
  if (tm.tag === 'Abs' && !tm.type && fty.tag === 'VPi' && !tm.plicity && fty.plicity) {
    const v = VVar(local.index);
    const term = check(extend(local, fty.name, fty.type, true, true, true, v), tm, fty.body(v));
    return Abs(fty.plicity, fty.name, quote(fty.type, local.index, false), term);
  }
  if (tm.tag === 'Let') {
    let vty;
    let val;
    let type;
    if (tm.type) {
      type = check(localInType(local), tm.type, VType);
      vty = evaluate(type, local.vs);
      val = check(local, tm.val, vty);
    } else {
      [val, vty] = synth(local, tm.val);
      type = quote(vty, local.index, false);
    }
    const body = check(extend(local, tm.name, vty, false, tm.plicity, false, evaluate(val, local.vs)), tm.body, ty);
    return Let(tm.plicity, tm.name, type, val, body);
  }
  const [term, ty2] = synth(local, tm);
  try {
    log(() => `unify ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}`);
    metaPush();
    unify(local.index, ty2, ty);
    metaDiscard();
    return term;
  } catch(err) {
    if (!(err instanceof TypeError)) throw err;
    try {
      metaPop();
      metaPush();
      const [ty2inst, ms] = inst(local.ts, local.vs, ty2); 
      log(() => `unify-inst ${showTermS(ty2inst, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}`);
      unify(local.index, ty2inst, ty);
      metaDiscard();
      return foldl((a, m) => App(a, true, m), term, ms);
    } catch {
      if (!(err instanceof TypeError)) throw err;
      metaPop();
      return terr(`failed to unify ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}: ${err.message}`);
    }
  }
};

const freshPi = (ts: EnvT, vs: EnvV, x: Name, impl: Plicity): Val => {
  const a = newMeta(ts);
  const va = evaluate(a, vs);
  const b = newMeta(extendT(ts, va, true, impl, false));
  return VPi(impl, x, va, v => evaluate(b, extendV(vs, v)));
};

const synth = (local: Local, tm: S.Term): [Term, Val] => {
  log(() => `synth ${S.showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  if (tm.tag === 'Sort') return [Sort(tm.sort), VType];
  if (tm.tag === 'Enum') return [Enum(tm.num), VType];
  if (tm.tag === 'Desc') return [Desc, VType];
  if (tm.tag === 'Elem') {
    const total = tm.total === null ? tm.num + 1 : tm.total;
    if (!(tm.num < total)) return terr(`invalid elem: ${S.showTerm(tm)}`);
    return [Elem(tm.num, total), VEnum(total)];
  }
  if (tm.tag === 'Var') {
    const i = indexOf(local.namesSurface, tm.name);
    if (i < 0) {
      const entry = globalGet(tm.name);
      if (!entry) return terr(`global ${tm.name} not found`);
      return [Global(tm.name), entry.type];
    } else {
      const [entry, j] = indexT(local.ts, i) || terr(`var out of scope ${S.showTerm(tm)}`);
      if (entry.plicity && !local.inType) return terr(`erased parameter ${S.showTerm(tm)} used`);
      return [Var(j), entry.type];
    }
  }
  if (tm.tag === 'Hole') {
    const t = newMeta(local.ts);
    const vt = evaluate(newMeta(local.ts), local.vs);
    return [t, vt];
  }
  if (tm.tag === 'App') {
    const [left, ty] = synth(local, tm.left);
    const [right, rty, ms] = synthapp(local, ty, tm.plicity, tm.right, tm);
    return [App(foldl((f, a) => App(f, true, a), left, ms), tm.plicity, right), rty];
  }
  if (tm.tag === 'Abs') {
    if (tm.type) {
      const type = check(localInType(local), tm.type, VType);
      const vtype = evaluate(type, local.vs);
      const [body, rt] = synth(extend(local, tm.name, vtype, true, tm.plicity, false, VVar(local.index)), tm.body);
      const pi = evaluate(Pi(tm.plicity, tm.name, type, quote(rt, local.index + 1, false)), local.vs);
      return [Abs(tm.plicity, tm.name, type, body), pi];
    } else {
      const pi = freshPi(local.ts, local.vs, tm.name, tm.plicity);
      const term = check(local, tm, pi);
      return [term, pi];
    }
  }
  if (tm.tag === 'Let') {
    let vty;
    let val;
    let type;
    if (tm.type) {
      type = check(localInType(local), tm.type, VType);
      vty = evaluate(type, local.vs);
      val = check(local, tm.val, vty);
    } else {
      [val, vty] = synth(local, tm.val);
      type = quote(vty, local.index, false);
    }
    const [body, rt] = synth(extend(local, tm.name, vty, false, tm.plicity, false, evaluate(val, local.vs)), tm.body);
    return [Let(tm.plicity, tm.name, type, val, body), rt];
  }
  if (tm.tag === 'Pi') {
    const type = check(localInType(local), tm.type, VType);
    const body = check(extend(local, tm.name, evaluate(type, local.vs), true, false, false, VVar(local.index)), tm.body, VType);
    return [Pi(tm.plicity, tm.name, type, body), VType];
  }
  if (tm.tag === 'Sigma') {
    const type = check(localInType(local), tm.type, VType);
    const body = check(extend(local, tm.name, evaluate(type, local.vs), true, false, false, VVar(local.index)), tm.body, VType);
    return [Sigma(tm.name, type, body), VType];
  }
  if (tm.tag === 'Pair') {
    const [fst, fstty] = synth(local, tm.fst);
    const [snd, sndty] = synth(local, tm.snd);
    const ty = VSigma('_', fstty, _ => sndty);
    const qty = quote(ty, local.index, false);
    return [Pair(fst, snd, qty), ty];
  }
  if (tm.tag === 'Fst') {
    const [term, ty] = synth(local, tm.term);
    const fty = force(ty);
    if (fty.tag !== 'VSigma') return terr(`not a sigma type in fst: ${S.showTerm(tm)}`);
    return [Fst(term), fty.type];
  }
  if (tm.tag === 'Snd') {
    const [term, ty] = synth(local, tm.term);
    const fty = force(ty);
    if (fty.tag !== 'VSigma') return terr(`not a sigma type in snd: ${S.showTerm(tm)}`);
    return [Snd(term), fty.body(vfst(evaluate(term, local.vs)))];
  }
  if (tm.tag === 'Ann') {
    const type = check(localInType(local), tm.type, VType);
    const vtype = evaluate(type, local.vs);
    const term = check(local, tm.term, vtype);
    return [Let(false, 'x', type, term, Var(0)), vtype];
  }
  if (tm.tag === 'UnsafeCast') {
    if (tm.type) {
      const type = check(localInType(local), tm.type, VType);
      const vt = evaluate(type, local.vs);
      const [val] = synth(local, tm.val);
      return [UnsafeCast(type, val), vt];
    } else {
      const type = newMeta(local.ts);
      const vt = evaluate(type, local.vs);
      const [val] = synth(local, tm.val);
      return [UnsafeCast(type, val), vt];
    }
  }
  if (tm.tag === 'EnumInd') {
    if (tm.args.length !== tm.num)
      return terr(`invalid enum induction, cases do not match: ${S.showTerm(tm)}`);
    const prop = check(localInType(local), tm.prop, VPi(false, '_', VEnum(tm.num), _ => VType));
    const P = evaluate(prop, local.vs);
    const term = check(local, tm.term, VEnum(tm.num));
    const args = tm.args.map((x, i) => check(local, x, vapp(P, false, VElem(i, tm.num))));
    return [EnumInd(tm.num, prop, term, args), vapp(P, false, evaluate(term, local.vs))];
  }
  return terr(`cannot synth ${S.showTerm(tm)}`);
};

const synthapp = (local: Local, ty_: Val, plicity: Plicity, tm: S.Term, tmall: S.Term): [Term, Val, List<Term>] => {
  log(() => `synthapp ${showTermS(ty_, local.names, local.index)} ${plicity ? '-' : ''}@ ${S.showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const ty = force(ty_);
  if (ty.tag === 'VPi' && ty.plicity && !plicity) {
    const m = newMeta(local.ts);
    const vm = evaluate(m, local.vs);
    const [rest, rt, l] = synthapp(local, ty.body(vm), plicity, tm, tmall);
    return [rest, rt, Cons(m, l)];
  }
  if (ty.tag === 'VPi' && ty.plicity === plicity) {
    const right = check(plicity ? localInType(local) : local, tm, ty.type);
    const rt = ty.body(evaluate(right, local.vs));
    return [right, rt, Nil];
  }
  // TODO fix the following
  if (ty.tag === 'VNe' && ty.head.tag === 'HMeta') {
    const a = freshMetaId();
    const b = freshMetaId();
    const pi = VPi(plicity, '_', VNe(HMeta(a), ty.args), () => VNe(HMeta(b), ty.args));
    unify(local.index, ty, pi);
    return synthapp(local, pi, plicity, tm, tmall);
  }
  return terr(`invalid type or plicity mismatch in synthapp in ${S.showTerm(tmall)}: ${showTermQ(ty, local.index)} ${plicity ? '-' : ''}@ ${S.showTerm(tm)}`);
};

export const typecheck = (tm: S.Term): [Term, Val] => {
  const [etm, ty] = synth(localEmpty, tm);
  const ztm = zonk(etm, Nil, 0);
  if (isUnsolved(ztm))
    return terr(`elaborated term was unsolved: ${showSurfaceZ(ztm)}`);
  if (config.verify) verify(ztm);
  return [ztm, ty];
};

export const typecheckDefs = (ds: S.Def[], allowRedefinition: boolean = false): Name[] => {
  log(() => `typecheckDefs ${ds.map(x => x.name).join(' ')}`);
  const xs: Name[] = [];
  if (!allowRedefinition) {
    for (let i = 0; i < ds.length; i++) {
      const d = ds[i];
      if (d.tag === 'DDef' && globalGet(d.name))
        return terr(`cannot redefine global ${d.name}`);
    }
  }
  for (let i = 0; i < ds.length; i++) {
    const d = ds[i];
    log(() => `typecheckDefs ${S.showDef(d)}`);
    if (d.tag === 'DDef') {
      const [tm_, ty] = typecheck(d.value);
      const tm = zonk(tm_);
      log(() => `set ${d.name} = ${showTerm(tm)}`);
      globalSet(d.name, tm, evaluate(tm, Nil), ty);
      xs.push(d.name);
    }
  }
  return xs;
};

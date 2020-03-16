import { Term, Pi, Type, Let, Abs, App, Global, Var, showTerm } from './syntax';
import { EnvV, Val, showTermQ, VType, force, evaluate, extendV, VVar, quote, showEnvV, showTermS } from './domain';
import { Nil, List, Cons, listToString, indexOf } from './utils/list';
import { Ix, Name } from './names';
import { terr } from './utils/util';
import { unify } from './unify';
import { Plicity } from './surface';
import * as S from './surface';
import { log, config } from './config';
import { globalGet, globalSet } from './globalenv';
import { toCore, showTerm as showTermC } from './core/syntax';
import { typecheck as typecheckC } from './core/typecheck';
import * as CD from './core/domain';

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

interface Local {
  names: List<Name>;
  namesSurface: List<Name>;
  ts: EnvT;
  vs: EnvV;
  index: Ix;
  inType: boolean;
}
const localEmpty: Local = { names: Nil, namesSurface: Nil, ts: Nil, vs: Nil, index: 0, inType: false };
const extend = (l: Local, name: Name, ty: Val, bound: boolean, plicity: Plicity, inserted: boolean, val: Val, inType: boolean = l.inType): Local => ({
  names: Cons(name, l.names),
  namesSurface: inserted ? l.namesSurface : Cons(name, l.namesSurface),
  ts: extendT(l.ts, ty, bound, plicity, inserted),
  vs: extendV(l.vs, val),
  index: l.index + 1,
  inType,
});
const localInType = (l: Local, inType: boolean = true): Local => ({
  names: l.names,
  namesSurface: l.namesSurface,
  ts: l.ts,
  vs: l.vs,
  index: l.index,
  inType,
});
const showLocal = (l: Local, full: boolean = false): string =>
  `Local(${l.index}, ${l.inType}, ${showEnvT(l.ts, l.index, full)}, ${showEnvV(l.vs, l.index, full)}, ${listToString(l.names)}, ${listToString(l.namesSurface)})`;

const check = (local: Local, tm: S.Term, ty: Val): Term => {
  log(() => `check ${S.showTerm(tm)} : ${showTermS(ty, local.names, local.index)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const fty = force(ty);
  if (tm.tag === 'Type' && fty.tag === 'VType') return Type;
  if (tm.tag === 'Abs' && !tm.type && fty.tag === 'VPi' && tm.plicity === fty.plicity) {
    const v = VVar(local.index);
    const body = check(extend(local, tm.name, fty.type, true, fty.plicity, false, v), tm.body, fty.body(v));
    return Abs(tm.plicity, tm.name, quote(fty.type, local.index, false), body);
  }
  if (tm.tag === 'Abs' && !tm.type && fty.tag === 'VPi' && !tm.plicity && fty.plicity) {
    const v = VVar(local.index);
    const term = check(extend(local, fty.name, fty.type, true, true, true, v), tm, fty.body(v));
    return Abs(fty.plicity, fty.name, quote(fty.type, local.index, false), term);
  }
  if (tm.tag === 'Let') {
    const [val, vty] = synth(local, tm.val);
    const body = check(extend(local, tm.name, vty, false, tm.plicity, false, evaluate(val, local.vs)), tm.body, ty);
    return Let(tm.plicity, tm.name, val, body);
  }
  const [etm, ty2] = synth(local, tm);
  try {
    unify(local.index, ty2, ty);
    return etm;
  } catch(err) {
    if (!(err instanceof TypeError)) throw err;
    return terr(`failed to unify ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}: ${err.message}`);
  }
};

const synth = (local: Local, tm: S.Term): [Term, Val] => {
  log(() => `synth ${S.showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  if (tm.tag === 'Type') return [Type, VType];
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
  if (tm.tag === 'App') {
    const [left, ty] = synth(local, tm.left);
    const [right, rty] = synthapp(local, ty, tm.plicity, tm.right, tm);
    return [App(left, tm.plicity, right), rty];
  }
  if (tm.tag === 'Abs' && tm.type) {
    const type = check(localInType(local), tm.type, VType);
    const vtype = evaluate(type, local.vs);
    const [body, rt] = synth(extend(local, tm.name, vtype, true, tm.plicity, false, VVar(local.index)), tm.body);
    const pi = evaluate(Pi(tm.plicity, tm.name, type, quote(rt, local.index + 1, false)), local.vs);
    return [Abs(tm.plicity, tm.name, type, body), pi];
  }
  if (tm.tag === 'Let') {
    const [val, vty] = synth(local, tm.val);
    const [body, rt] = synth(extend(local, tm.name, vty, false, tm.plicity, false, evaluate(val, local.vs)), tm.body);
    return [Let(tm.plicity, tm.name, val, body), rt];
  }
  if (tm.tag === 'Pi') {
    const type = check(localInType(local), tm.type, VType);
    const body = check(extend(local, tm.name, evaluate(type, local.vs), true, false, false, VVar(local.index)), tm.body, VType);
    return [Pi(tm.plicity, tm.name, type, body), VType];
  }
  if (tm.tag === 'Ann') {
    const type = check(localInType(local), tm.type, VType);
    const vtype = evaluate(type, local.vs);
    const term = check(local, tm.term, vtype);
    return [term, vtype];
  }
  return terr(`cannot synth ${S.showTerm(tm)}`);
};

export const synthapp = (local: Local, ty: Val, plicity: Plicity, tm: S.Term, tmall: S.Term): [Term, Val] => {
  log(() => `synthapp ${showTermS(ty, local.names, local.index)} ${plicity ? '-' : ''}@ ${S.showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const fty = force(ty);
  if (fty.tag === 'VPi' && fty.plicity === plicity) {
    const right = check(plicity ? localInType(local) : local, tm, fty.type);
    const rt = fty.body(evaluate(right, local.vs));
    return [right, rt];
  }
  return terr(`invalid type or plicity mismatch in synthapp in ${S.showTerm(tmall)}: ${showTermQ(ty, local.index)} ${plicity ? '-' : ''}@ ${S.showTerm(tm)}`);
};

export const typecheck = (tm: S.Term, local: Local = localEmpty): [Term, Val] =>
  synth(local, tm);

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
      const [tm, ty] = typecheck(d.value);
      log(() => `set ${d.name} = ${showTerm(tm)}`);
      const zty = quote(ty, 0, false);
      const ctm = toCore(tm);
      if (config.checkCore) {
        log(() => `typecheck in core: ${showTermC(ctm)}`);
        const cty = typecheckC(ctm);
        log(() => `core type: ${showTermC(CD.quote(cty, 0, false))}`);
        globalSet(d.name, tm, evaluate(tm, Nil), ty, ctm, CD.evaluate(ctm, Nil), cty);
      } else {
        globalSet(d.name, tm, evaluate(tm, Nil), ty, ctm, CD.evaluate(ctm, Nil), CD.evaluate(toCore(zty), Nil));
      }
      xs.push(d.name);
    }
  }
  return xs;
};

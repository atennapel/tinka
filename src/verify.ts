import { Term, Pi, showTerm } from './syntax';
import { EnvV, Val, showTermQ, VType, force, evaluate, extendV, VVar, quote, showEnvV, showTermS, VEnum, VPi, vapp, VElem, vproj } from './domain';
import { Nil, List, Cons, listToString } from './utils/list';
import { Ix, Name } from './names';
import { terr } from './utils/utils';
import { Plicity } from './surface';
import { log, config } from './config';
import { globalGet } from './globalenv';
import { conv } from './conv';
import { primType } from './prims';

type EntryT = { type: Val, bound: boolean, plicity: Plicity };
type EnvT = List<EntryT>;
const extendT = (ts: EnvT, val: Val, bound: boolean, plicity: Plicity): EnvT =>
  Cons({ type: val, bound, plicity }, ts);
const showEnvT = (ts: EnvT, k: Ix = 0, full: boolean = false): string =>
  listToString(ts, entry => `${entry.bound ? '' : 'd '}${entry.plicity ? 'e ' : ''}${showTermQ(entry.type, k, full)}`);
const indexT = (ts: EnvT, ix: Ix): [EntryT, Ix] | null => {
  let l = ts;
  let i = 0;
  while (l.tag === 'Cons') {
    if (ix === 0) return [l.head, i];
    i++;
    ix--;
    l = l.tail;
  }
  return null;
};

export interface Local {
  names: List<Name>;
  ts: EnvT;
  vs: EnvV;
  index: Ix;
  inType: boolean;
}
export const localEmpty: Local = { names: Nil, ts: Nil, vs: Nil, index: 0, inType: false };
export const extend = (l: Local, name: Name, ty: Val, bound: boolean, plicity: Plicity, val: Val, inType: boolean = l.inType): Local => ({
  names: Cons(name, l.names),
  ts: extendT(l.ts, ty, bound, plicity),
  vs: extendV(l.vs, val),
  index: l.index + 1,
  inType,
});
export const localInType = (l: Local, inType: boolean = true): Local => ({
  names: l.names,
  ts: l.ts,
  vs: l.vs,
  index: l.index,
  inType,
});
export const showLocal = (l: Local, full: boolean = false): string =>
  `Local(${l.index}, ${l.inType}, ${showEnvT(l.ts, l.index, full)}, ${showEnvV(l.vs, l.index, full)}, ${listToString(l.names)})`;

const check = (local: Local, tm: Term, ty: Val): void => {
  log(() => `check ${showTerm(tm)} : ${showTermS(ty, local.names, local.index)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const ty2 = synth(local, tm);
  try {
    log(() => `conv ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}`);
    conv(local.index, ty2, ty);
    return;
  } catch(err) {
    if (!(err instanceof TypeError)) throw err;
    return terr(`failed to conv ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}: ${err.message}`);
  }
};

const synth = (local: Local, tm: Term): Val => {
  log(() => `synth ${showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  if (tm.tag === 'Enum') return VType;
  if (tm.tag === 'Prim') return primType(tm.name);
  if (tm.tag === 'Elem' && tm.num < tm.total) return VEnum(tm.total);
  if (tm.tag === 'Global') {
    const entry = globalGet(tm.name);
    if (!entry) return terr(`global ${tm.name} not found`);
    return entry.type;
  }
  if (tm.tag === 'Var') {
    const i = tm.index;
    const [entry] = indexT(local.ts, i) || terr(`var out of scope ${showTerm(tm)}`);
    if (entry.plicity && !local.inType) return terr(`erased parameter ${showTerm(tm)} used`);
    return entry.type;
  }
  if (tm.tag === 'App') {
    const ty = synth(local, tm.left);
    const rty = synthapp(local, ty, tm.plicity, tm.right, tm);
    return rty;
  }
  if (tm.tag === 'Abs') {
    check(localInType(local), tm.type, VType);
    const vtype = evaluate(tm.type, local.vs);
    const rt = synth(extend(local, tm.name, vtype, true, tm.plicity, VVar(local.index)), tm.body);
    const pi = evaluate(Pi(tm.plicity, tm.name, tm.type, quote(rt, local.index + 1, false)), local.vs);
    return pi;
  }
  if (tm.tag === 'Let') {
    check(localInType(local), tm.type, VType);
    const vty = evaluate(tm.type, local.vs);
    check(local, tm.val, vty);
    const rt = synth(extend(local, tm.name, vty, false, tm.plicity, evaluate(tm.val, local.vs)), tm.body);
    return rt;
  }
  if (tm.tag === 'Pi') {
    check(localInType(local), tm.type, VType);
    check(extend(local, tm.name, evaluate(tm.type, local.vs), true, false, VVar(local.index)), tm.body, VType);
    return VType;
  }
  if (tm.tag === 'Sigma') {
    check(localInType(local), tm.type, VType);
    check(extend(local, tm.name, evaluate(tm.type, local.vs), true, false, VVar(local.index)), tm.body, VType);
    return VType;
  }
  if (tm.tag === 'Pair') {
    check(localInType(local), tm.type, VType);
    const vt = evaluate(tm.type, local.vs);
    const vtf = force(vt);
    if (vtf.tag !== 'VSigma') return terr(`Pair with non-sigma type: ${showTerm(tm)} : ${showTermS(vtf, local.names, local.index)}`);
    if (tm.plicity !== vtf.plicity) return terr(`Pair with mismatched plicity (fst): ${showTerm(tm)} : ${showTermS(vtf, local.names, local.index)}`);
    if (tm.plicity2 !== vtf.plicity2) return terr(`Pair with mismatched plicity (snd): ${showTerm(tm)} : ${showTermS(vtf, local.names, local.index)}`);
    if (tm.plicity && tm.plicity2) return terr(`Pair cannot be erased in both element: ${showTerm(tm)} : ${showTermS(vtf, local.names, local.index)}`);
    check(vtf.plicity ? localInType(local) : local, tm.fst, vtf.type);
    check(vtf.plicity2 ? localInType(local) : local, tm.snd, vtf.body(evaluate(tm.fst, local.vs)));
    return vt;
  }
  if (tm.tag === 'Proj') {
    const ty = synth(local, tm.term);
    const fty = force(ty);
    if (fty.tag !== 'VSigma') return terr(`not a sigma type in ${tm.proj}: ${showTerm(tm)}`);
    if (tm.proj === 'fst' && fty.plicity && !local.inType) return terr(`cannot call fst on erased sigma: ${showTerm(tm)}`);
    return tm.proj === 'fst' ? fty.type : fty.body(vproj('fst', evaluate(tm.term, local.vs)));
  }
  if (tm.tag === 'EnumInd') {
    if (tm.args.length !== tm.num)
      return terr(`invalid enum induction, cases do not match: ${showTerm(tm)}`);
    check(localInType(local), tm.prop, VPi(false, '_', VEnum(tm.num), _ => VType));
    const P = evaluate(tm.prop, local.vs);
    check(local, tm.term, VEnum(tm.num));
    for (let i = 0; i < tm.args.length; i++)
      check(local, tm.args[i], vapp(P, false, VElem(i, tm.num)));
    return vapp(P, false, evaluate(tm.term, local.vs));
  }
  return terr(`cannot synth ${showTerm(tm)}`);
};

const synthapp = (local: Local, ty_: Val, plicity: Plicity, tm: Term, tmall: Term): Val => {
  log(() => `synthapp ${showTermS(ty_, local.names, local.index)} ${plicity ? '-' : ''}@ ${showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const ty = force(ty_);
  if (ty.tag === 'VPi' && ty.plicity === plicity) {
    check(plicity ? localInType(local) : local, tm, ty.type);
    const rt = ty.body(evaluate(tm, local.vs));
    return rt;
  }
  return terr(`invalid type or plicity mismatch in synthapp in ${showTerm(tmall)}: ${showTermQ(ty, local.index)} ${plicity ? '-' : ''}@ ${showTerm(tm)}`);
};

export const verify = (tm: Term): Val => {
  const ty = synth(localEmpty, tm);
  return ty;
};

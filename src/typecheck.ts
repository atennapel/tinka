import { Term, showTerm, Pi, showSurface } from './syntax';
import { EnvV, Val, showTermQ, VType, force, evaluate, extendV, VVar, quote, showEnvV, showTermS } from './domain';
import { Nil, index, List, Cons, listToString } from './utils/list';
import { Ix, Name } from './names';
import { terr } from './utils/util';
import { unify } from './unify';
import { Plicity } from './surface';
import { log, config } from './config';
import { globalGet } from './globalenv';

type EntryT = { type: Val, bound: boolean, plicity: Plicity, inserted: boolean };
type EnvT = List<EntryT>;
const extendT = (ts: EnvT, val: Val, bound: boolean, plicity: Plicity, inserted: boolean): EnvT =>
  Cons({ type: val, bound, plicity, inserted }, ts);
const showEnvT = (ts: EnvT, k: Ix = 0, full: boolean = false): string =>
  listToString(ts, entry => `${entry.bound ? '' : 'd '}${entry.plicity ? 'e ' : ''}${entry.inserted ? 'i ' : ''}${showTermQ(entry.type, k, full)}`);

interface Local {
  names: List<Name>;
  ts: EnvT;
  vs: EnvV;
  index: Ix;
  inType: boolean;
}
const localEmpty: Local = { names: Nil, ts: Nil, vs: Nil, index: 0, inType: false };
const extend = (l: Local, name: Name, ty: Val, bound: boolean, plicity: Plicity, inserted: boolean, val: Val, inType: boolean = l.inType): Local => ({
  names: Cons(name, l.names),
  ts: extendT(l.ts, ty, bound, plicity, inserted),
  vs: extendV(l.vs, val),
  index: l.index + 1,
  inType,
});
const localInType = (l: Local, inType: boolean = true): Local => ({
  names: l.names,
  ts: l.ts,
  vs: l.vs,
  index: l.index,
  inType,
});
const showLocal = (l: Local, full: boolean = false): string =>
  `Local(${l.index}, ${l.inType}, ${showEnvT(l.ts, l.index, full)}, ${showEnvV(l.vs, l.index, full)}, ${listToString(l.names)})`;

const check = (local: Local, tm: Term, ty: Val): void => {
  log(() => `check ${showSurface(tm, local.names)} : ${showTermS(ty, local.names, local.index)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const ty2 = synth(local, tm);
  try {
    unify(local.index, ty2, ty);
  } catch(err) {
    if (!(err instanceof TypeError)) throw err;
    terr(`failed to unify ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}: ${err.message}`);
  }
};

const synth = (local: Local, tm: Term): Val => {
  log(() => `synth ${showSurface(tm, local.names)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  if (tm.tag === 'Type') return VType;
  if (tm.tag === 'Var') {
    const entry = index(local.ts, tm.index) || terr(`var out of scope ${showTerm(tm)}`);
    if (entry.plicity && !local.inType) return terr(`erased parameter ${showTerm(tm)} used`);
    return entry.type;
  }
  if (tm.tag === 'Global') {
    const entry = globalGet(tm.name);
    if (!entry) return terr(`global ${tm.name} not found`);
    return entry.type;
  }
  if (tm.tag === 'App') {
    const ty = force(synth(local, tm.left));
    if (ty.tag === 'VPi' && ty.plicity === tm.plicity) {
      check(local, tm.right, ty.type);
      return ty.body(evaluate(tm.right, local.vs));
    }
    return terr(`invalid type or plicity mismatch in synthapp in ${showTerm(tm)}: ${showTermQ(ty, local.index)} ${tm.plicity ? '-' : ''}@ ${showTerm(tm.right)}`);
  }
  if (tm.tag === 'Abs' && tm.type) {
    check(localInType(local), tm.type, VType);
    const type = evaluate(tm.type, local.vs);
    const rt = synth(extend(local, tm.name, type, true, tm.plicity, false, VVar(local.index)), tm.body);
    return evaluate(Pi(tm.plicity, tm.name, tm.type, quote(rt, local.index + 1, false)), local.vs);
  }
  if (tm.tag === 'Let') {
    const vty = synth(local, tm.val);
    const rt = synth(extend(local, tm.name, vty, true, tm.plicity, false, VVar(local.index)), tm.body);
    return rt;
  }
  if (tm.tag === 'Pi') {
    check(localInType(local), tm.type, VType);
    check(extend(local, tm.name, evaluate(tm.type, local.vs), true, tm.plicity, false, VVar(local.index)), tm.body, VType);
    return VType;
  }
  return terr(`cannot synth ${showTerm(tm)}`);
};

export const typecheck = (tm: Term, local: Local = localEmpty): Val =>
  synth(local, tm);

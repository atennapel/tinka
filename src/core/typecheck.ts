import { Term, showTerm, Pi } from './syntax';
import { EnvV, Val, showTermQ, VType, force, evaluate, extendV, VVar, quote, showEnvV } from './domain';
import { Nil, index, List, Cons, listToString } from '../utils/list';
import { Ix } from '../names';
import { terr } from '../utils/util';
import { unify } from './unify';
import { Plicity } from '../surface';
import { log, config } from '../config';
import { globalGet } from '../globalenv';

type EntryT = { type: Val, plicity: Plicity };
type EnvT = List<EntryT>;
const extendT = (ts: EnvT, val: Val, plicity: Plicity): EnvT =>
  Cons({ type: val, plicity }, ts);
const showEnvT = (ts: EnvT, k: Ix = 0, full: boolean = false): string =>
  listToString(ts, entry => `${entry.plicity ? 'e ' : ''}${showTermQ(entry.type, k, full)}`);

interface Local {
  ts: EnvT;
  vs: EnvV;
  index: Ix;
  inType: boolean;
}
const localEmpty: Local = { ts: Nil, vs: Nil, index: 0, inType: false };
const extend = (l: Local, ty: Val, plicity: Plicity, val: Val, inType: boolean = l.inType): Local => ({
  ts: extendT(l.ts, ty, plicity),
  vs: extendV(l.vs, val),
  index: l.index + 1,
  inType,
});
const localInType = (l: Local, inType: boolean = true): Local => ({
  ts: l.ts,
  vs: l.vs,
  index: l.index,
  inType,
});
const showLocal = (l: Local, full: boolean = false): string =>
  `Local(${l.index}, ${l.inType}, ${showEnvT(l.ts, l.index, full)}, ${showEnvV(l.vs, l.index, full)})`;

const check = (local: Local, tm: Term, ty: Val): void => {
  log(() => `check ${showTerm(tm)} : ${showTermQ(ty)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  const ty2 = synth(local, tm);
  try {
    unify(local.index, ty2, ty);
  } catch(err) {
    if (!(err instanceof TypeError)) throw err;
    terr(`failed to unify ${showTermQ(ty2, local.index)} ~ ${showTermQ(ty, local.index)}: ${err.message}`);
  }
};

const synth = (local: Local, tm: Term): Val => {
  log(() => `synth ${showTerm(tm)}${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  if (tm.tag === 'Type') return VType;
  if (tm.tag === 'Var') {
    const entry = index(local.ts, tm.index) || terr(`var out of scope ${showTerm(tm)}`);
    if (entry.plicity && !local.inType) return terr(`erased parameter ${showTerm(tm)} used`);
    return entry.type;
  }
  if (tm.tag === 'Global') {
    const entry = globalGet(tm.name);
    if (!entry) return terr(`global ${tm.name} not found`);
    return entry.coretype;
  }
  if (tm.tag === 'App') {
    const ty = force(synth(local, tm.left));
    if (ty.tag === 'VPi' && ty.plicity === tm.plicity) {
      check(tm.plicity ? localInType(local) : local, tm.right, ty.type);
      return ty.body(evaluate(tm.right, local.vs));
    }
    return terr(`invalid type or plicity mismatch in synthapp in ${showTerm(tm)}: ${showTermQ(ty, local.index)} ${tm.plicity ? '-' : ''}@ ${showTerm(tm.right)}`);
  }
  if (tm.tag === 'Abs') {
    check(localInType(local), tm.type, VType);
    const type = evaluate(tm.type, local.vs);
    const rt = synth(extend(local, type, tm.plicity, VVar(local.index)), tm.body);
    return evaluate(Pi(tm.plicity, tm.type, quote(rt, local.index + 1, false)), local.vs);
  }
  if (tm.tag === 'Let') {
    check(localInType(local), tm.type, VType);
    const vty = evaluate(tm.type, local.vs);
    check(extend(local, vty, tm.plicity, VVar(local.index)), tm.body, vty);
    return vty;
  }
  if (tm.tag === 'Pi') {
    check(localInType(local), tm.type, VType);
    check(extend(local, evaluate(tm.type, local.vs), false, VVar(local.index)), tm.body, VType);
    return VType;
  }
  if (tm.tag === 'Fix') {
    check(localInType(local), tm.type, VType);
    const vt = evaluate(tm.type, local.vs);
    check(extend(local, evaluate(tm.type, local.vs), false, VVar(local.index)), tm.body, vt);
    return vt;
  }
  if (tm.tag === 'Data') {
    tm.cons.forEach(t => check(extend(local, VType, false, VVar(local.index)), t, VType));
    return VType;
  }
  if (tm.tag === 'Roll') {
    check(localInType(local), tm.type, VType);
    const vt = force(evaluate(tm.type, local.vs));
    if (vt.tag === 'VFix') {
      check(local, tm.term, vt.body(vt));
      return vt;
    }
    return terr(`fix type expected in ${showTerm(tm)}: ${showTermQ(vt, local.index)}`);
  }
  if (tm.tag === 'Unroll') {
    const vt = force(synth(local, tm.term));
    if (vt.tag === 'VFix') return vt.body(vt);
    return terr(`fix type expected in ${showTerm(tm)}: ${showTermQ(vt, local.index)}`);
  }
  if (tm.tag === 'Con') {
    check(localInType(local), tm.type, VType);
    const vtype = evaluate(tm.type, local.vs);
    const ft = force(vtype);
    if (ft.tag !== 'VData') return terr(`not a datatype in con: ${showTerm(tm)}`);
    if (ft.cons.length !== tm.total) return terr(`cons amount mismatch: ${showTerm(tm)}`);
    if (!ft.cons[tm.index]) return terr(`not a valid constructor: ${showTerm(tm)}`);
    const con = ft.cons[tm.index](vtype);
    const rt = synthconargs(local, con, tm.args);
    if (force(rt).tag !== 'VData') return terr(`constructor was not fully applied: ${showTerm(tm)}`);
    return rt;
  }
  return terr(`cannot synth ${showTerm(tm)}`);
};

const synthconargs = (local: Local, ty_: Val, args: [Term, Plicity][]): Val => {
  log(() => `synthconargs ${showTermQ(ty_, local.index)} @ [${args.map(([t, p]) => `${p ? '-' : ''}${showTerm(t)}`).join(' ')}]${config.showEnvs ? ` in ${showLocal(local)}` : ''}`);
  if (args.length === 0) return ty_;
  const ty = force(ty_);
  const head = args[0];
  if (ty.tag === 'VPi' && ty.plicity === head[1]) {
    check(ty.plicity ? localInType(local) : local, head[0], ty.type);
    const rt = ty.body(evaluate(head[0], local.vs));
    return synthconargs(local, rt, args.slice(1));
  }
  return terr(`invalid type or plicity mismatch in synthconargs`);
};

export const typecheck = (tm: Term, local: Local = localEmpty): Val =>
  synth(local, tm);

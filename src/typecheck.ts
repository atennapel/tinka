import { Term, Pi, Let, Abs, App, Global, Var, showTerm, showSurface, isUnsolved, showSurfaceZ, Sigma, Pair, Prim, Proj, Sort } from './syntax';
import { EnvV, Val, showTermQ, VType, force, evaluate, extendV, VVar, quote, showEnvV, showTermS, zonk, VPi, VNe, HMeta, VSigma, vproj, showTermSZ } from './domain';
import { Nil, List, Cons, listToString, indexOf, mapIndex, filter, foldr, foldl, zipWith, toArray, index } from './utils/list';
import { Ix, Name } from './names';
import { terr } from './utils/utils';
import { unify } from './unify';
import { Plicity } from './surface';
import * as S from './surface';
import { log, config } from './config';
import { globalGet, globalSet, globalMap } from './globalenv';
import { freshMeta, freshMetaId, metaPush, metaDiscard, metaPop } from './metas';
import { verify } from './verify';
import { primType } from './prims';
import * as E from './erased';

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
  const ty = force(ty_);
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
  if (tm.tag === 'Sort' && fty === VType) return Sort(tm.sort);
  if (tm.tag === 'Hole') {
    const x = newMeta(local.ts);
    if (tm.name) {
      const y = tm.name === '_' ? `_${instanceId++}` : tm.name;
      if (holes[y]) return terr(`named hole used more than once: _${y}`);
      holes[y] = [evaluate(x, local.vs), ty, local, y.startsWith('_')];
    }
    return x;
  }
  if (tm.tag === 'Pair' && fty.tag === 'VSigma') {
    if (tm.plicity !== fty.plicity) return terr(`Pair with mismatched plicity (fst): ${S.showTerm(tm)} : ${showTermS(fty, local.names, local.index)}`);
    if (tm.plicity2 !== fty.plicity2) return terr(`Pair with mismatched plicity (snd): ${S.showTerm(tm)} : ${showTermS(fty, local.names, local.index)}`);
    if (tm.plicity && tm.plicity2) return terr(`Pair cannot be erased in both element: ${S.showTerm(tm)} : ${showTermS(fty, local.names, local.index)}`);
    const fst = check(fty.plicity ? localInType(local) : local, tm.fst, fty.type);
    const snd = check(fty.plicity2 ? localInType(local) : local, tm.snd, fty.body(evaluate(fst, local.vs)));
    return Pair(tm.plicity, tm.plicity2, fst, snd, quote(ty, local.index, false));
  }
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
      [val, vty] = synth(tm.plicity ? localInType(local) : local, tm.val);
      type = quote(vty, local.index, false);
    }
    const body = check(extend(local, tm.name, vty, false, tm.plicity, false, evaluate(val, local.vs)), tm.body, ty);
    return Let(tm.plicity, tm.name, type, val, body);
  }
  const [term, ty2] = synth(local, tm);
  try {
    log(() => `unify ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}`);
    metaPush();
    holesPush();
    unify(local.index, ty2, ty);
    metaDiscard();
    holesPush();
    return term;
  } catch(err) {
    if (!(err instanceof TypeError)) throw err;
    try {
      metaPop();
      holesPop();
      metaPush();
      holesPush();
      const [ty2inst, ms] = inst(local.ts, local.vs, ty2); 
      log(() => `unify-inst ${showTermS(ty2inst, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}`);
      unify(local.index, ty2inst, ty);
      metaDiscard();
      holesDiscard();
      return foldl((a, m) => App(a, true, m), term, ms);
    } catch (err) {
      if (!(err instanceof TypeError)) throw err;
      metaPop();
      holesPop();
      return terr(`failed to unify in ${S.showTerm(tm)}:  ${showTermS(ty2, local.names, local.index)} ~ ${showTermS(ty, local.names, local.index)}: ${err.message}`);
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
  if (tm.tag === 'Prim') return [Prim(tm.name), primType(tm.name)];
  if (tm.tag === 'Sort') return [tm, VType];
  if (tm.tag === 'Var') {
    const i = indexOf(local.namesSurface, tm.name);
    if (i < 0) {
      const entry = globalGet(tm.name);
      if (!entry) return terr(`global ${tm.name} not found`);
      if (entry.plicity && !local.inType) return terr(`erased global ${S.showTerm(tm)} used`);
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
    if (tm.name) {
      const x = tm.name === '_' ? `_${instanceId++}` : tm.name;
      if (holes[x]) return terr(`named hole used more than once: _${x}`);
      holes[x] = [evaluate(t, local.vs), vt, local, x.startsWith('_')];
    }
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
      [val, vty] = synth(tm.plicity ? localInType(local) : local, tm.val);
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
    return [Sigma(tm.plicity, tm.plicity2, tm.name, type, body), VType];
  }
  if (tm.tag === 'Pair') {
    if (tm.plicity && tm.plicity2) return terr(`Pair cannot be erased in both element: ${S.showTerm(tm)}`);
    const [fst, fstty] = synth(tm.plicity ? localInType(local) : local, tm.fst);
    const [snd, sndty] = synth(tm.plicity2 ? localInType(local) : local, tm.snd);
    const ty = VSigma(tm.plicity, tm.plicity2, '_', fstty, _ => sndty);
    const qty = quote(ty, local.index, false);
    return [Pair(tm.plicity, tm.plicity2, fst, snd, qty), ty];
  }
  if (tm.tag === 'Proj') {
    const [term, ty] = synth(local, tm.term);
    const fty = force(ty);
    if (fty.tag !== 'VSigma') return terr(`not a sigma type in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
    const proj = tm.proj;
    if (proj.tag === 'PCore') {
      const tag = proj.proj;
      if (tag === 'fst' && fty.plicity && !local.inType) return terr(`cannot call fst on erased sigma: ${S.showTerm(tm)}`);
      if (tag === 'snd' && fty.plicity2 && !local.inType) return terr(`cannot call snd on erased sigma: ${S.showTerm(tm)}`);
      const e = Proj(tag, term);
      return tag === 'fst' ? [e, fty.type] : [e, fty.body(vproj('fst', evaluate(term, local.vs)))];
    } else if (proj.tag === 'PIndex') {
      let c = term;
      let t: Val = fty;
      let v: Val = evaluate(term, local.vs);
      for (let i = 0; i < proj.index; i++) {
        if (t.tag !== 'VSigma') return terr(`not a sigma type in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
        if (t.plicity2 && !local.inType) return terr(`trying to project from erased element of sigma in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
        c = Proj('snd', c);
        t = t.body(vproj('fst', v));
        v = vproj('snd', v);
      }
      if (t.tag !== 'VSigma') return terr(`not a sigma type in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
      if (t.plicity && !local.inType) return terr(`trying to project from erased element of sigma in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
      return [Proj('fst', c), t.type];
    } else if (proj.tag === 'PName') {
      let c = term;
      let t: Val = fty;
      let v: Val = evaluate(term, local.vs);
      while (true) {
        if (t.tag !== 'VSigma') return terr(`not a sigma type or name not found in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
        if (t.name === proj.name) break;
        if (t.plicity2 && !local.inType) return terr(`trying to project from erased element of sigma in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
        c = Proj('snd', c);
        t = t.body(vproj('fst', v));
        v = vproj('snd', v);
      }
      if (t.tag !== 'VSigma') return terr(`not a sigma type in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
      if (t.plicity && !local.inType) return terr(`trying to project from erased element of sigma in ${S.showTerm(tm)}: ${showTermS(fty, local.names, local.index)}`);
      return [Proj('fst', c), t.type];
    }
  }
  if (tm.tag === 'Ann') {
    const type = check(localInType(local), tm.type, VType);
    const vtype = evaluate(type, local.vs);
    const term = check(local, tm.term, vtype);
    return [Let(false, 'x', type, term, Var(0)), vtype];
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

const tryUnify = (local: Local, ty1: Val, ty2: Val): TypeError | null => {
  try {
    metaPush();
    holesPush();
    unify(local.index, ty1, ty2);
    metaDiscard();
    holesDiscard();
    return null;
  } catch (err) {
    if (!(err instanceof TypeError)) throw err;
    metaPop();
    holesPop();
    return new TypeError(`failed to unify in ${showTermS(ty1, local.names, local.index)} ~ ${showTermS(ty2, local.names, local.index)}: ${err.message}`);
  }
};

let recInstanceCounter = 0;

const searchSingleInstance = (name: Name, ctm: Term, wtm: Val, local: Local, cty: Val, wty: Val): TypeError | null => {
  // try equality
  metaPush();
  const result1 = tryUnify(local, cty, wty);
  if (!result1) {
    log(() => `found match ${name}`);
    const v = evaluate(ctm, local.vs);
    unify(local.index, wtm, v);
    metaDiscard();
    return null;
  }
  metaPop();

  // try equality with instantiation
  metaPush();
  const [vty, ms] = inst(local.ts, local.vs, cty);
  const result2 = tryUnify(local, vty, wty);
  if (!result2) {
    log(() => `found instantiated match ${name}`);
    const v = evaluate(foldl((a, m) => App(a, true, m), ctm, ms), local.vs);
    unify(local.index, wtm, v);
    metaDiscard();
    return null;
  }
  metaPop();

  // try recursive
  metaPush();
  const [vty2, ms2] = inst(local.ts, local.vs, cty);
  const fvty = force(vty2);
  if (fvty.tag === 'VPi' && !fvty.plicity) {
    const exlocal = extend(local, fvty.name, fvty.type, true, false, false, VVar(local.index));
    const res = tryUnify(exlocal, fvty.body(VVar(local.index)), wty);
    if (!res) {
      log(() => `found potential recursive match ${name}`);
      metaPush();
      const rname = `rec${recInstanceCounter++}`;
      const mtm = newMeta(local.ts);
      const vmtm = evaluate(mtm, local.vs);

      try {
        searchInstance(rname, vmtm, fvty.type, local);
        const res = tryUnify(local, fvty.body(vmtm), wty);
        if (!res) {
          log(() => `found recursive match ${name}`);
          const v = evaluate(App(foldl((a, m) => App(a, true, m), ctm, ms2), false, mtm), local.vs);
          unify(local.index, wtm, v);
          metaDiscard();
          return null;
        } else throw res;
      } catch (err) {
        if (!(err instanceof TypeError)) throw err;
        metaPop();
        return err;
      }
    }
  }
  metaPop();

  return new TypeError(`no match found`);
};

const invalidInstances: string[] = ['id', 'indVoid', 'caseVoid'];

const searchInstance = (name: Name, tm_: Val, ty_: Val, local: Local): void => {
  log(() => `searchInstance _${name} = ${showTermSZ(tm_, local.names, local.vs, local.index, false)} : ${showTermSZ(ty_, local.names, local.vs, local.index, false)}`);
  const ty = force(ty_);
  const tm = force(tm_);
  if (ty.tag === 'VNe' && ty.head.tag === 'HMeta') return terr(`cannot solve instance _${name}, expected type is a meta: ${showTermS(ty_, local.names, local.index)}`);
  if (tm.tag === 'VNe' && tm.head.tag !== 'HMeta') return terr(`cannot solve instance _${name}, expected term is not a meta: ${showTermS(tm_, local.names, local.index)}`);
  let c = local.ts;
  let i = -1;
  log(() => `search locals`);
  while (c.tag === 'Cons') {
    const entry = c.head;
    c = c.tail;
    i++;
    if (entry.plicity) continue; // TODO: improve this
    const res = searchSingleInstance(index(local.names, i) || `$${i}`, Var(i), tm_, local, entry.type, ty_);
    if (!res) return;
  }
  const env = globalMap();
  const ns = Object.keys(env).reverse();
  log(() => `search globals`);
  for (let i = 0, l = ns.length; i < l; i++) { // TODO: ensure reverse insertion order
    const x = ns[i];
    if (invalidInstances.includes(x)) continue; // TODO!
    const entry = globalGet(x);
    if (!entry) continue;
    log(() => `try ${x}`);
    if (entry.plicity) continue; // TODO: improve this
    const res = searchSingleInstance(x, Global(x), tm_, local, entry.type, ty_);
    if (!res) return;
  }
  return terr(`failed to find instance for _${name} = ${showTermS(tm_, local.names, local.index)} : ${showTermS(ty_, local.names, local.index)}`);
};

let instanceId: Ix = 0;
type HoleInfo = [Val, Val, Local, boolean];
let holesStack: { [key:string]: HoleInfo }[] = [];
let holes: { [key:string]: HoleInfo } = {};
const holesPush = (): void => {
  const old = holes;
  holesStack.push(holes);
  holes = {};
  for (let k in old) holes[k] = old[k];
};
const holesPop = (): void => {
  const x = holesStack.pop();
  if (!x) return;
  holes = x;
};
const holesDiscard = (): void => { holesStack.pop() };
const holesReset = (): void => { holesStack = []; holes = {} };

export const typecheck = (tm: S.Term, plicity: Plicity = false): [Term, Val, E.Term] => {
  holesReset();
  const [etm, ty] = synth(plicity ? localInType(localEmpty) : localEmpty, tm);
  const entries = Object.entries(holes);

  const insts = entries.filter(([_, info]) => info[3]);
  for (let i = 0, l = insts.length; i < l; i++) {
    const [x, [t, v, local]] = insts[i];
    searchInstance(x, t, v, local);
  }

  const ztm = zonk(etm, Nil, 0);

  const holeprops = entries.filter(([_, info]) => !info[3]);
  if (holeprops.length > 0) {
    const strtype = showTermSZ(ty);
    const strterm = showSurface(ztm);
    const str = holeprops.map(([x, [t, v, local, inst]]) => {
      const all = zipWith(([x, v], { bound: def, type: ty, inserted, plicity }) => [x, v, def, ty, inserted, plicity] as [Name, Val, boolean, Val, boolean, Plicity], zipWith((x, v) => [x, v] as [Name, Val], local.names, local.vs), local.ts);
      const allstr = toArray(all, ([x, v, b, t, _, p]) => `${p ? `{${x}}` : x} : ${showTermSZ(t, local.names, local.vs, local.index)}${b ? '' : ` = ${showTermSZ(v, local.names, local.vs, local.index)}`}`).join('\n');
      return `\n${inst ? 'inst ' : ''}_${x} : ${showTermSZ(v, local.names, local.vs, local.index)} = ${showTermSZ(t, local.names, local.vs, local.index)}\nlocal:\n${allstr}\n`;
    }).join('\n');
    return terr(`unsolved holes\ntype: ${strtype}\nterm: ${strterm}\n${str}`);
  }

  if (isUnsolved(ztm)) // do I have to check types as well? Or maybe only metas?
    return terr(`elaborated term was unsolved: ${showSurfaceZ(ztm)}`);

  const erased = verify(ztm);

  return [ztm, ty, erased[1]];
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
      try {
        const [tm_, ty, er] = typecheck(d.value, d.plicity);
        const tm = zonk(tm_);
        log(() => `set ${d.name} = ${showTerm(tm)}`);
        globalSet(d.name, tm, evaluate(tm, Nil), ty, d.plicity, er);

        const i = xs.indexOf(d.name);
        if (i >= 0) xs.splice(i, 1);
        xs.push(d.name);
      } catch (err) {
        err.message = `type error in def ${d.name}: ${err.message}`;
        throw err;
      }
    }
  }
  return xs;
};

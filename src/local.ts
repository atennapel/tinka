import { Erasure, Expl, Mode } from './mode';
import { Ix, Lvl, Name } from './names';
import { cons, List, nil } from './utils/List';
import { EnvV, quote, show, Val, VVar } from './values';
import * as S from './surface';
import { Core } from './core';

export interface EntryT {
  readonly type: Val;
  readonly erased: Erasure;
  readonly mode: Mode;
  readonly bound: boolean;
  readonly inserted: boolean;
}
export const EntryT = (type: Val, erased: Erasure, mode: Mode, bound: boolean, inserted: boolean): EntryT =>
  ({ type, bound, mode, erased, inserted });

export type EnvT = List<EntryT>;

export const indexEnvT = (ts: EnvT, ix: Ix): [EntryT, Ix, number] | null => {
  let l: EnvT = ts;
  let i = 0;
  let erased = 0;
  while (l.isCons()) {
    if (l.head.inserted) {
      l = l.tail;
      i++;
      continue;
    }
    if (ix === 0) return [l.head, i, erased];
    if (l.head.erased) erased++;
    i++;
    ix--;
    l = l.tail;
  }
  return null;
};

export type Path = List<[Erasure, Mode, Name, Core, Core | null]>;

export class Local {

  readonly erased: Erasure;
  readonly level: Lvl;
  readonly ns: List<Name>;
  readonly nsSurface: List<Name>;
  readonly ts: EnvT;
  readonly vs: EnvV;
  readonly path: Path;

  constructor(
    erased: Erasure,
    level: Lvl,
    ns: List<Name>,
    nsSurface: List<Name>,
    ts: EnvT,
    vs: EnvV,
    path: Path,
  ) {
    this.erased = erased;
    this.level = level;
    this.ns = ns;
    this.nsSurface = nsSurface;
    this.ts = ts;
    this.vs = vs;
    this.path = path;
  }

  private static _empty: Local;
  static empty() {
    if (Local._empty === undefined) Local._empty = new Local(false, 0, nil, nil, nil, nil, nil);
    return Local._empty;  
  }

  bind(erased: Erasure, mode: Mode, name: Name, ty: Val): Local {
    return new Local(
      this.erased,
      this.level + 1,
      cons(name, this.ns),
      cons(name, this.nsSurface),
      cons(EntryT(ty, erased, mode, true, false), this.ts),
      cons(VVar(this.level), this.vs),
      cons([erased, mode, name, quote(ty, this.level), null], this.path),
    );
  }
  insert(erased: Erasure, mode: Mode, name: Name, ty: Val): Local {
    return new Local(
      this.erased,
      this.level + 1,
      cons(name, this.ns),
      this.nsSurface,
      cons(EntryT(ty, erased, mode, true, true), this.ts),
      cons(VVar(this.level), this.vs),
      cons([erased, mode, name, quote(ty, this.level), null], this.path),
    );
  }
  define(erased: Erasure, name: Name, ty: Val, val: Val, qty: Core, qval: Core): Local {
    return new Local(
      this.erased,
      this.level + 1,
      cons(name, this.ns),
      cons(name, this.nsSurface),
      cons(EntryT(ty, erased, Expl, false, false), this.ts),
      cons(val, this.vs),
      cons([erased, Expl, name, qty, qval], this.path),
    );
  }

  undo(): Local {
    if (this.level === 0) return this;
    return new Local(
      this.erased,
      this.level - 1,
      (this.ns as any).tail,
      (this.nsSurface as any).tail,
      (this.ts as any).tail,
      (this.vs as any).tail,
      (this.path as any).tail,
    );
  }

  inType(): Local {
    return new Local(
      true,
      this.level,
      this.ns,
      this.nsSurface,
      this.ts,
      this.vs,
      this.path,
    );
  }

  toString(): string {
    return this.ts.toString(e => `${e.bound ? '' : 'd '}${showV(this, e.type)}`);
  }

}

export const showV = (local: Local, val: Val): string => S.showVal(val, local.level, false, local.ns);
export const showValCore = (local: Local, val: Val): string => show(val, local.level);

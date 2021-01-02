import { Expl, Mode } from './mode';
import { Ix, Lvl, Name } from './names';
import { Usage } from './usage';
import { cons, List, nil } from './utils/List';
import { EnvV, show, Val, VVar } from './values';

export interface EntryT {
  readonly type: Val;
  readonly usage: Usage;
  readonly mode: Mode;
  readonly bound: boolean;
  readonly inserted: boolean;
}
export const EntryT = (type: Val, usage: Usage, mode: Mode, bound: boolean, inserted: boolean): EntryT =>
  ({ type, bound, mode, usage, inserted });

export type EnvT = List<EntryT>;

export const indexEnvT = (ts: EnvT, ix: Ix): [EntryT, Ix] | null => {
  let l: EnvT = ts;
  let i = 0;
  while (l.isCons()) {
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

export class Local {

  readonly level: Lvl;
  readonly ns: List<Name>;
  readonly nsSurface: List<Name>;
  readonly ts: EnvT;
  readonly vs: EnvV;

  constructor(
    level: Lvl,
    ns: List<Name>,
    nsSurface: List<Name>,
    ts: EnvT,
    vs: EnvV,
  ) {
    this.level = level;
    this.ns = ns;
    this.nsSurface = nsSurface;
    this.ts = ts;
    this.vs = vs;
  }

  private static _empty: Local;
  static empty() {
    if (Local._empty === undefined) Local._empty = new Local(0, nil, nil, nil, nil);
    return Local._empty;  
  }

  bind(usage: Usage, mode: Mode, name: Name, ty: Val): Local {
    return new Local(
      this.level + 1,
      cons(name, this.ns),
      cons(name, this.nsSurface),
      cons(EntryT(ty, usage, mode, true, false), this.ts),
      cons(VVar(this.level), this.vs),
    );
  }
  insert(usage: Usage, mode: Mode, name: Name, ty: Val): Local {
    return new Local(
      this.level + 1,
      cons(name, this.ns),
      this.nsSurface,
      cons(EntryT(ty, usage, mode, true, true), this.ts),
      cons(VVar(this.level), this.vs),
    );
  }
  define(usage: Usage, name: Name, ty: Val, val: Val): Local {
    return new Local(
      this.level + 1,
      cons(name, this.ns),
      cons(name, this.nsSurface),
      cons(EntryT(ty, usage, Expl, false, false), this.ts),
      cons(val, this.vs),
    );
  }

  unsafeUndo(): Local {
    return new Local(
      this.level - 1,
      (this.ns as any).tail,
      (this.nsSurface as any).tail,
      (this.ts as any).tail,
      (this.vs as any).tail,
    );
  }

}

export const showVal = (local: Local, val: Val): string => show(val, local.level);

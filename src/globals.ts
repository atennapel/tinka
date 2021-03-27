import { Core } from './core';
import { elaborate } from './elaboration';
import { Erasure } from './mode';
import { Name } from './names';
import { parse } from './parser';
import { nil } from './utils/List';
import { impossible, loadFileSync } from './utils/utils';
import { evaluate, Val } from './values';
import { verify } from './verification';

export interface GlobalEntry {
  readonly type: Val;
  readonly value: Val;
  readonly etype: Core;
  readonly term: Core;
  readonly erased: Erasure;
}

export type Globals = { [key: string]: GlobalEntry };

let globals: Globals = {};

export const resetGlobals = (): void => { globals = {} };

export const getGlobal = (name: Name): GlobalEntry => {
  const entry = globals[name];
  if (!entry) return impossible(`undefined global in getGlobal: ${name}`);
  return entry;
};

export const getGlobals = (): Globals => globals;

export const setGlobal = (name: Name, type: Val, value: Val, etype: Core, term: Core, erased: boolean): void => {
  globals[name] = { type, value, etype, term, erased };
};

export const deleteGlobal = (name: Name): void => {
  delete globals[name];
};

export const loadGlobal = (x: string): GlobalEntry | null => {
  if (globals[x]) return globals[x];
  const sc = loadFileSync(`lib/${x}`);
  if (sc instanceof Error) return null;
  const e = parse(sc);
  const [tm, ty] = elaborate(e);
  verify(tm);
  setGlobal(x, evaluate(ty, nil), evaluate(tm, nil), ty, tm, false);
  return getGlobal(x);
};

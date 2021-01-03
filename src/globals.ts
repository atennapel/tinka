import { elaborate } from './elaboration';
import { parse } from './parser';
import { typecheck } from './typecheck';
import { nil } from './utils/List';
import { loadFileSync } from './utils/utils';
import { evaluate, Val } from './values';

export interface EntryG {
  val: Val,
  type: Val,
}

type Globals = { [key: string]: EntryG };

let globals: Globals = {};

export const globalReset = () => {
  globals = {};
};

export const globalGet = (x: string): EntryG | null => globals[x] || null;
export const globalSet = (x: string, val: Val, type: Val): void => {
  globals[x] = { val, type };
};

export const globalLoad = (x: string): EntryG | null => {
  if (globals[x]) return globals[x];
  const sc = loadFileSync(x);
  if (sc instanceof Error) return null;
  const e = parse(sc);
  const [tm, ty] = elaborate(e);
  typecheck(tm);
  globalSet(x, evaluate(tm, nil), evaluate(ty, nil));
  return globalGet(x);
};
